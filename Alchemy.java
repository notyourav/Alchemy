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
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Scanner;
import ghidra.app.decompiler.ClangTokenGroup;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.emulator.EmulatorHelper;
import ghidra.app.script.GhidraScript;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.model.DomainFolder;
import ghidra.framework.options.ToolOptions;
import ghidra.framework.plugintool.util.OptionsService;
import ghidra.util.InvalidNameException;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateFileException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.FileInUseException;
import ghidra.util.exception.VersionException;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.FunctionPrototype;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighSymbol;
import ghidra.program.model.pcode.LocalSymbolMap;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.pcode.VarnodeAST;
import ghidra.pcode.opbehavior.*;

/**
 * the decompilation process: createInitialContext(); while (true) {
 * generateFile(); compileFile(); updateContext(); }
 * 
 * The initial context refers to Ghidra's decompilation output as a starting
 * point.
 * 
 * During the file generation step, we refer to the current context and create a
 * new attempt.
 * 
 * The context keeps track of what permutations we have tried. TODO: diff pcode
 * between iterations TODO: we can work more efficiently by creating several
 * changes in parallel the obvious difficulty will be making sure these changes
 * don't conflict with each other
 */

public class Alchemy extends GhidraScript {
	static final boolean ECHO_TO_STDOUT = true;
	static final int NUM_ITERATIONS = 1;
	static final String TEMP_FOLDER = "~Alchemy";
	static final String COMPILER_PATH = "/Users/theo/tmc/tools/agbcc/bin/agbcc";
	static final String INCLUDE_PATH = "/Users/theo/tmc/tools/agbcc/include";
	static final String ASSEMBLER_PATH = "/System/Volumes/Data/opt/devkitpro/devkitARM/bin/arm-none-eabi-as";
	static final String COMPILER_OPTIONS = "-O2";

	Context ctx = new Context();
	DecompInterface idec;
	HighFunction target;
	ClangTokenGroup docroot;

	// base typedefs that are the same across all contexts
	StringBuilder typedefs = new StringBuilder();
	Hashtable<Composite, String> structs = new Hashtable<Composite, String>();
	Hashtable<String, DataType> globals = new Hashtable<String, DataType>();
	ArrayList<Function> ext_functions = new ArrayList<Function>();

	public class Context {
		Program program;
		int transactionHandle;

		Function function;

		long step;

		/**
		 * Update the decompilation context with the current file.
		 * 
		 * @param file File to add
		 * @return Resulting program
		 */
		void update(File f) {
			cleanupCtx();

			try {
				ctx.program = ghidra.app.util.importer.AutoImporter.importByUsingBestGuess(f,
						getProjectRootFolder().getFolder(TEMP_FOLDER), this, new MessageLog(), monitor);
			} catch (CancelledException | DuplicateNameException | InvalidNameException | VersionException
					| IOException e) {
				e.printStackTrace();
			}

			// Start a new transaction for the entire step
			transactionHandle = program.startTransaction("Alchemy");

			analyzeAll(program);
			FunctionIterator fiter = program.getListing().getFunctions(true);
			if (!fiter.hasNext()) {
				throw new RuntimeException("A compile error occured and no function was generated!");
			}
			function = fiter.next();

			ctx.step++;
		}

		void cleanupCtx() {
			if (program != null) {
				// end the transaction so we can delete the old program
				program.endTransaction(transactionHandle, true);
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
		typedefs.append("#include <stdint.h>\n");
		typedefs.append("typedef uint8_t u8;\n");
		typedefs.append("typedef uint16_t u16;\n");
		typedefs.append("typedef uint32_t u32;\n");
		typedefs.append("typedef uint64_t u64;\n");
		typedefs.append("typedef int8_t s8;\n");
		typedefs.append("typedef int16_t s16;\n");
		typedefs.append("typedef int32_t s32;\n");
		typedefs.append("typedef int64_t s64;\n");
	}

	String generateFile() throws IOException {
		//PrintWriter pw = new PrintWriter(tu);
		StringBuilder pw = new StringBuilder();
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

		// add typedefs
		pw.append(typedefs);

		// add struct defs
		for (String v : structs.values()) {
			pw.append(v);
		}

		// add globals
		globals.forEach((k, v) -> {
			pw.append("extern " + getTypeName(v) + " " + k + ";\n");
		});
		
		// add functions
		for (Function f : ext_functions) {
			pw.append("extern " + getTypeName(f.getReturnType()) + " " + f.getName() + "();\n" );
		}

		// print function
		pw.append(proto);
		pw.append(" {\n");

		for (String s : body.split("\n")) {
			pw.append("\t" + s + "\n");
		}
		pw.append("}\n");

		if (ECHO_TO_STDOUT) {
			println("=====File Contents Begin=====");
			print(pw.toString());
			println("=====File Contents End=====");
		}
		
		return pw.toString();
	}

	/**
	 * Construct the prototype of the function
	 * 
	 * @return
	 */
	String constructPrototype() {
		FunctionPrototype proto = target.getFunctionPrototype();
		String fnName = target.getFunction().getName();
		String retType = getTypeName(proto.getReturnType());

		StringBuilder sb = new StringBuilder();
		sb.append(retType + " " + fnName + "(");

		int num = proto.getNumParams();
		String[] args = new String[num];
		// print arguments
		for (int i = 0; i < num; ++i) {
			HighSymbol hs = proto.getParam(i);
			String argType = getTypeName(hs.getDataType());
			args[i] = argType + " " + hs.getName();
		}
		sb.append(String.join(", ", args) + ")");
		return sb.toString();
	}

	/**
	 * Construct the body of the function
	 * 
	 * @return
	 */
	String constructBody() {
		StringBuilder sb = new StringBuilder();
		
		Iterator<HighSymbol> global_iter = target.getGlobalSymbolMap().getSymbols();
		while (global_iter.hasNext()) {
			HighSymbol s = global_iter.next();
			DataType dt = s.getDataType();

			if (dt instanceof Composite) {
				// todo: why is this needed? doesnt it get registered when globals are read?
				registerComposite(dt);
			}
			globals.putIfAbsent(s.getName(), dt);
		}

		Iterator<HighSymbol> local_iter = target.getLocalSymbolMap().getSymbols();
		while (local_iter.hasNext()) {
			HighSymbol local = local_iter.next();

			// already printed in prologue
			if (local.isParameter())
				continue;

			sb.append(getTypeName(local.getDataType()) + " " + local.getName() + ";\n");
		}

		ArrayList<PcodeBlockBasic> blocks = target.getBasicBlocks();
		for (PcodeBlockBasic block : blocks) {
			Iterator<PcodeOp> children = block.getIterator();
			while (children.hasNext()) {
				PcodeOp c = children.next();
				switch (c.getOpcode()) {
				case PcodeOp.CALL:
					Varnode in0 = c.getInput(0);
					Function f = currentProgram.getFunctionManager().getFunctionAt(in0.getAddress());
					registerFunction(f);
					sb.append(f.getName() + "();\n");
				}
			}
		}

		// EmulatorHelper emuHelper = new EmulatorHelper(currentProgram);

		return sb.toString();
	}

	/**
	 * Retrieve the C type name of a Ghidra DataType
	 * 
	 * @param dt
	 * @return type
	 */
	String getTypeName(DataType dt) {
		if (dt instanceof Array) {
			dt = ((Array) dt).getDataType();
		}

		if (dt instanceof Pointer) {
			DataType pointedTo = dt;
			int p_cnt = 0;
			while (pointedTo instanceof Pointer) {
				p_cnt++;
				pointedTo = ((Pointer) pointedTo).getDataType();
			}
			
			return (pointedTo instanceof Structure ? "struct " : "") + getTypeName(pointedTo) + "*".repeat(p_cnt);
		}

		if (dt instanceof BuiltInDataType) {
			return builtinToTypedef(dt);
		}

		if (dt instanceof DefaultDataType) {
			return "u8";
		}

		if (dt instanceof Composite) {
			return registerComposite(dt);
		}

		if (dt instanceof Enum) {
			switch (dt.getLength()) {
			case 1:
				return "u8";
			case 2:
				return "u16";
			case 4:
				return "u32";
			}
		}

		if (dt instanceof BitFieldDataType) {
			switch (dt.getLength()) {
			case 1:
				return "u8";
			case 2:
				return "u16";
			case 4:
				return "u32";
			}
		}

		throw new RuntimeException("Cannot create a type name for DataType " + dt.getClass());
	}

	/**
	 * Convert built in data types to typedefs
	 * 
	 * @param dt DataType to convert
	 * @return typedef name
	 */
	String builtinToTypedef(DataType dt) {
		if (dt instanceof VoidDataType) {
			return "void";
		}

		if (dt instanceof AbstractIntegerDataType && ((AbstractIntegerDataType) dt).isSigned()) {
			switch (dt.getLength()) {
			case 1:
				return "s8";
			case 2:
				return "s16";
			case 4:
				return "s32";
			case 8:
				return "s64";
			}
		} else {
			switch (dt.getLength()) {
			case 1:
				return "u8";
			case 2:
				return "u16";
			case 4:
				return "u32";
			case 8:
				return "u64";
			}
		}

		throw new RuntimeException("Builtin DataType " + dt.getName() + " could not be read.");
	}
	
	String registerComposite(DataType dt) {
		// todo: support union

		if (!(dt instanceof Composite)) {
			throw new RuntimeException("DataType is not a Composite: " + dt.getName());
		}

		if (dt instanceof Union) {
			throw new RuntimeException("Sorry, unions are not supported yet.");
		}

		Composite s = (Composite) dt;

		if (!structs.containsKey(s)) {
			// placeholder so Struct containing Struct* doesn't cause recursion
			structs.put(s, "");

			StringBuilder sb = new StringBuilder();
			sb.append("typedef struct " + s.getName() + " {\n");
			for (DataTypeComponent c : s.getComponents()) {
				String ctype = getTypeName(c.getDataType());
				if (ctype == null) {
					ctype = "u8";
				}

				String name = c.getFieldName() != null ? c.getFieldName() : c.getDefaultFieldName();
				String arrCnt = c.getDataType() instanceof Array
						? "[" + ((Array) c.getDataType()).getNumElements() + "]"
						: "";
				sb.append("\t" + ctype + " " + name + arrCnt + ";\n");
			}
			sb.append("} " + s.getName() + ";\n");

			structs.put(s, sb.toString());
		}

		return s.getName();
	}
	
	void registerFunction(Function f) {
		ext_functions.add(f);
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
			String cmd[] = { "/bin/sh", "-c", command };
			Process process = Runtime.getRuntime().exec(cmd);

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
	File compile(String tu) {
		File bin = null;
		try {
			bin = File.createTempFile("alchemy", ".o");
		} catch (IOException e) {
			e.printStackTrace();
		}

		String cpp_command = String.format("cc -E -I%s - ", INCLUDE_PATH);
		String cc_command = String.format("%s %s", COMPILER_PATH, COMPILER_OPTIONS);
		String as_command = String.format("%s -o %s", ASSEMBLER_PATH, bin.getAbsoluteFile());
		
		sh("echo '" + tu + "' | " + cpp_command + " | " + cc_command + " | " + as_command);
		
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

		// Get the focused function in Ghidra.
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

		for (int i = 0; i < NUM_ITERATIONS; ++i) {
			String tu = generateFile();

			File bin = compile(tu);
			ctx.update(bin);
		}
		ctx.cleanupCtx();

		try {
			folder.delete();
		} catch (FileInUseException e) {
			print("Warning: unable to delete temp folder in database.\n");
		}
	}
}
