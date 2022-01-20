//Alchemy: Iterative decompiler
//@author 
//@category sleigh
//@keybinding 
//@menupath 
//@toolbar applications-science.png
//

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Dictionary;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Scanner;
import java.util.stream.Stream;

import org.python.google.common.collect.Lists;

import ghidra.app.decompiler.ClangTokenGroup;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.plugin.processors.sleigh.ConstructState;
import ghidra.app.script.GhidraScript;
import ghidra.app.util.importer.MessageLog;
import ghidra.docking.settings.Settings;
import ghidra.framework.model.DomainFolder;
import ghidra.framework.options.ToolOptions;
import ghidra.framework.plugintool.util.OptionsService;
import ghidra.util.InvalidNameException;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateFileException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.FileInUseException;
import ghidra.util.exception.VersionException;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.FunctionPrototype;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighSymbol;
import ghidra.program.model.pcode.LocalSymbolMap;
import ghidra.program.model.pcode.PcodeBlock;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.pcode.VarnodeAST;

public class Alchemy extends GhidraScript {

	static final int NUM_ITERATIONS = 1;
	static final String TEMP_FOLDER = "~Alchemy";
	static final String COMPILER_PATH = "/Users/theo/tmc/tools/agbcc/bin/agbcc";
	static final String ASSEMBLER_PATH = "/System/Volumes/Data/opt/devkitpro/devkitARM/bin/arm-none-eabi-as";
	static final String COMPILER_OPTIONS = "-O2";

	Context ctx = new Context();
	DecompInterface idec;
	HighFunction target;
	ClangTokenGroup docroot;

	// base typedefs that are the same across all contexts
	StringBuilder typedefs = new StringBuilder();
	Hashtable<Structure, String> structs = new Hashtable<Structure, String>();
	Hashtable<String, DataType> globals = new Hashtable<String, DataType>();
	
	
	public class Context {
		Program program;
		int programTID;
		Function function;

		long step;

		/**
		 * Update the decompilation context with the current file.
		 * 
		 * @param file File to add
		 * @return Resulting program
		 */
		void update(File f) {
			cleanup();

			try {
				ctx.program = ghidra.app.util.importer.AutoImporter.importByUsingBestGuess(f,
						getProjectRootFolder().getFolder(TEMP_FOLDER), this, new MessageLog(), monitor);
			} catch (CancelledException | DuplicateNameException | InvalidNameException | VersionException
					| IOException e) {
				e.printStackTrace();
			}

			// Start a new transaction for the entire step
			programTID = program.startTransaction("Alchemy");

			analyzeAll(program);
			function = program.getListing().getFunctions(true).next();

			ctx.step++;
		}

		// Cleanup temporary information
		void cleanup() {
			if (program != null) {
				program.endTransaction(programTID, true);
				program.release(this);
				try {
					program.getDomainFile().delete();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
	}

	void setupDefaultTypedefs() {
		typedefs.append("include <stdint.h>\n");
		typedefs.append("typedef uint8_t u8;\n");
		typedefs.append("typedef uint16_t u16;\n");
		typedefs.append("typedef uint32_t u32;\n");
		typedefs.append("typedef uint64_t u64;\n");
		typedefs.append("typedef int8_t s8;\n");
		typedefs.append("typedef int16_t s16;\n");
		typedefs.append("typedef int32_t s32;\n");
		typedefs.append("typedef int64_t s64;\n");
	}

	/*
	 * 
	 * What is our starting place for tackling non matchings? We need to associate
	 * specific differences with specific c features (e.g.: differences in a loop
	 * could be while/for)
	 * 
	 * We can work more efficiently by creating several changes in parallel before
	 * sending the TU off to the compiler, the obvious obstacle to this is making
	 * sure these changes don't conflict with each other. Changes which are likely
	 * to cause huge shifts in the generated code should run on their own.
	 * 
	 */
	void decompilerMain(Function lastAttempt, File tu) throws IOException {
		PrintWriter pw = new PrintWriter(tu);
//		for (int i = 0; i < proto.getNumParams(); ++i) {
//			HighSymbol hs = proto.getParam(i);
//			DataType dt = hs.getDataType();
//			if (dt instanceof BuiltInDataType) {
//			}
//		}

//		Iterator<HighSymbol> locals = target.getLocalSymbolMap().getSymbols();
//		while (locals.hasNext()) {
//			HighSymbol s = locals.next();
//			print(s.getDataType().getName() + " " + s.getName() + "\n");
//		}

		String proto = constructPrototype();
		String body = constructBody();


		// make sure we have collected the structures first!
		pw.append(typedefs);
		
		for (String v : structs.values()) {
			pw.append(v);
		}
		
		globals.forEach((k, v) -> {
			pw.append("extern " + getTypeName(v) + " " + k + ";\n");
		});
		
		pw.append(proto);
		pw.append(" {\n");
		
		pw.append(body);
		pw.append("}\n");
		pw.close();

		// print everything for debugging
		Scanner sc = new Scanner(tu);
		while (sc.hasNextLine()) {
			println(sc.nextLine());
		}
		sc.close();
	}

	String constructPrototype() {
		FunctionPrototype proto = target.getFunctionPrototype();
		String fnName = target.getFunction().getName();
		String retType = getTypeName(proto.getReturnType());

		StringBuilder sb = new StringBuilder();
		sb.append(retType + " " + fnName + "(");
		
		int num = proto.getNumParams();
		String[] args = new String[num];
		for (int i = 0; i < num; ++i) {
			HighSymbol hs = proto.getParam(i);
			String argType = getTypeName(hs.getDataType());
			args[i] = argType + " " + hs.getName();
		}
		sb.append(String.join(", ", args) + ")"); 		
		return sb.toString();
	}

	String constructBody() {
		Iterator<HighSymbol> syms = target.getGlobalSymbolMap().getSymbols();
		while (syms.hasNext()) {
			HighSymbol s = syms.next();
			DataType dt = s.getDataType();
			registerStruct(dt);
			globals.putIfAbsent(s.getName(), dt);
		}

		Iterator<VarnodeAST> vns = target.locRange();
		while (vns.hasNext()) {
			VarnodeAST v = vns.next();
			Iterator<PcodeOp> children = v.getDescendants();
			println(v.getPCAddress().toString());
			while (children.hasNext()) {
				PcodeOp c = children.next();
				println(c.getMnemonic());
			}
		}
		return "";
	}

	// Returns a data type from the database
	String getTypeName(DataType dt) {
		// Make sure the pointed to type is registered
		if (dt instanceof Pointer) {
			DataType pointedTo = dt;
			while (pointedTo instanceof Pointer) {
				pointedTo = ((Pointer) pointedTo).getDataType();
			}
			getTypeName(pointedTo);
			return dt.toString();
		}
		
		if (dt instanceof BuiltInDataType) {
			return builtinToCName(dt);
		}
		
		if (!(dt instanceof Structure)) {
			switch (dt.getLength()) {
				case 1: return "u8";
				case 2: return "u16";
				case 4: return "u32";
			}
		}
		
		return registerStruct(dt);
	}

	String builtinToCName(DataType dt) {
		if (dt instanceof VoidDataType) {
			return "void";
		} else if (dt instanceof SignedByteDataType) {
			return "s8";
		} else if (dt instanceof CharDataType || dt instanceof ByteDataType || dt instanceof BooleanDataType) {
			return "u8";
		} else if (dt instanceof IntegerDataType || dt instanceof SignedDWordDataType) {
			return "s32";
		} else if (dt instanceof UnsignedIntegerDataType || dt instanceof DWordDataType) {
			return "u32";
		} else if (dt instanceof ShortDataType || dt instanceof SignedWordDataType) {
			return "s16";
		} else if (dt instanceof UnsignedShortDataType || dt instanceof WordDataType) {
			return "u16";
		}

		print(String.format("Could not read type %s\n", dt.getName()));
		return null;
	}

	String registerStruct(DataType dt) {
		if (dt instanceof BuiltInDataType || !(dt instanceof Structure))
			return null;
		
		Structure s = (Structure) dt;
		
 		if (!structs.containsKey(s)) {
 			// placeholder so Struct containing Struct* doesn't cause recursion
 			structs.put(s, "");
 			
			StringBuilder sb = new StringBuilder();
			sb.append("typedef struct {\n");
			for (DataTypeComponent c : s.getComponents()) {
				String ctype = getTypeName(c.getDataType());
				if (ctype == null) {
					ctype = "u8";
				}
				String name = c.getFieldName() != null ? c.getFieldName() : c.getDefaultFieldName();
				sb.append("\t" + ctype + " " + name + ";\n");
			}
			sb.append( "} " + s.getName() + ";\n");
			
			structs.put(s, sb.toString());
		}

		return s.getName();
	}

	private DecompInterface setUpDecompiler(Program program) {
		DecompInterface decomplib = new DecompInterface();

		DecompileOptions options;
		options = new DecompileOptions();
		OptionsService service = state.getTool().getService(OptionsService.class);
		if (service != null) {
			ToolOptions opt = service.getOptions("Decompiler");
			options.grabFromToolAndProgram(null, opt, program);
		}
		decomplib.setOptions(options);

		decomplib.toggleCCode(true);
		decomplib.toggleSyntaxTree(true);
		decomplib.setSimplificationStyle("decompile");

		return decomplib;
	}

	public boolean decompileFunction(Function f, DecompInterface decomplib) {
		DecompileResults decompRes = decomplib.decompileFunction(f, decomplib.getOptions().getDefaultTimeout(),
				monitor);

		target = decompRes.getHighFunction();
		docroot = decompRes.getCCodeMarkup();

		if (target == null)
			return false;

		return true;
	}

	/**
	 * Run shell command
	 * 
	 * @param command The command to run
	 * @return exit value
	 */
	int sh(String command) {
		try {
			Process process = Runtime.getRuntime().exec(command);

			StringBuilder output = new StringBuilder();

			BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));

			String line;
			while ((line = reader.readLine()) != null) {
				output.append(line + "\n");
			}

			int exitVal = process.waitFor();
			print(output.toString());
			return exitVal;

		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}
		return 1;
	}

	/**
	 * Compile a translation unit.
	 * 
	 * @param tu File to compile.
	 * @return Resulting binary file
	 */
	File compile(File tu) {
		File asm = null;
		File bin = null;

		try {
			asm = File.createTempFile("alchemy", ".s");
			bin = File.createTempFile("alchemy", ".o");
		} catch (IOException e) {
			e.printStackTrace();
		}

		// compile
		sh(String.format("%s %s %s -o %s", COMPILER_PATH, COMPILER_OPTIONS, tu.getAbsoluteFile(),
				asm.getAbsoluteFile()));
		// assemble
		sh(String.format("%s %s -o %s", ASSEMBLER_PATH, asm.getAbsoluteFile(), bin.getAbsoluteFile()));
		return bin;
	}

	DomainFolder getFolder() throws Exception {
		DomainFolder root = getProjectRootFolder();
		try {
			root.createFolder(TEMP_FOLDER);
		} catch (DuplicateFileException e) {
		}
		return root.getFolder(TEMP_FOLDER);
	}

	public void run() throws Exception {
		DomainFolder folder = getFolder();
		setupDefaultTypedefs();

		// Highlighted function is our target
		Function fn = this.currentProgram.getListing().getFunctionContaining(currentAddress);
		if (fn == null) {
			print("Error: Must focus on a function to decompile.\n");
			return;
		}

		idec = setUpDecompiler(currentProgram);
		idec.openProgram(currentProgram);
		if (!decompileFunction(fn, idec)) {
			print("Error encountered while decompiling. Quitting.\n");
			return;
		}

		File tu = File.createTempFile("alchemy", ".c");
		print(tu.getAbsolutePath() + "\n");

		for (int i = 0; i < NUM_ITERATIONS; ++i) {
			decompilerMain(ctx.function, tu);

			File bin = compile(tu);
			ctx.update(bin);
		}
		ctx.cleanup();
		
		try {
		folder.delete();
		} catch (FileInUseException e) {
			print("Warning: unable to delete temp folder in database.\n");
		}
	}
}
