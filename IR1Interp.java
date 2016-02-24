// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
//---------------------------------------------------------------------------
// For CS322 W'16 (J. Li).
//
//
// Andrew McCann
// CS322 HW3
// Winter 2016
//

// IR1 interpreter. (A starter version)
//
//

import java.util.*;
import java.io.*;

import com.sun.org.apache.xpath.internal.operations.Bool;
import ir.*;

public class IR1Interp {

	static class IntException extends Exception {
		public IntException(String msg) {
			super(msg);
		}
	}

	//-----------------------------------------------------------------
	// Value Representation
	//-----------------------------------------------------------------
	//
	abstract static class Val {
	}

	// -- Integer values
	//
	static class IntVal extends Val {
		int i;

		IntVal(int i) {
			this.i = i;
		}

		public String toString() {
			return "" + i;
		}
	}

	// -- Boolean values
	//
	static class BoolVal extends Val {
		boolean b;

		BoolVal(boolean b) {
			this.b = b;
		}

		public String toString() {
			return "" + b;
		}
	}

	// -- String values
	//
	static class StrVal extends Val {
		String s;

		StrVal(String s) {
			this.s = s;
		}

		public String toString() {
			return s;
		}
	}

	// -- A special "undefined" value
	//
	static class UndVal extends Val {
		public String toString() {
			return "UndVal";
		}
	}

	//-----------------------------------------------------------------
	// Storage Organization
	//-----------------------------------------------------------------
	//

	// -- Global heap memory
	//
	static ArrayList<Val> memory;

	// -- Environment for tracking var, temp, and param's values
	//    (one copy per function invocation)
	//
	static class Env extends HashMap<String, Val> {
	}

	// Used to create the memory allocation that IR1 necessitates
	static Val undVal = new UndVal();


	//-----------------------------------------------------------------
	// Other Data Structures
	//-----------------------------------------------------------------
	//
	// GUIDE:
	//  You have control over these. Either define look-up tables for
	//  functions and labels, or searching functions.
	//

	// -- Useful global variables
	//
	static final int CONTINUE = -1;  // execution status
	static final int RETURN = -2;    // execution status
	static Val retVal = null;             // for return value passing

	// Structure to track function code block info
	static HashMap<String, IR1.Func> funcMap;

	// Structure to track location of labeldecs
	static class LabMap extends HashMap<String, Integer> {
	}

	// Map of label locations
	static HashMap<String, LabMap> labelMap;


	//-----------------------------------------------------------------
	// The Main Method
	//-----------------------------------------------------------------
	//
	public static void main(String[] args) throws Exception {
		if (args.length == 1) {
			FileInputStream stream = new FileInputStream(args[0]);
			IR1.Program p = new IR1Parser(stream).Program();
			stream.close();
			IR1Interp.execute(p);
		} else {
			System.out.println("You must provide an input file name.");
		}
	}

	//-----------------------------------------------------------------
	// Top-Level Nodes
	//-----------------------------------------------------------------
	//

	// Program ---
	//  Func[] funcs;
	//
	// GUIDE:
	// 1. Establish the look-up tables (if you plan to use them).
	// 2. Look up or search for function '_main'.
	// 3. Start interpreting from '_main' with an empty Env.
	//
	public static void execute(IR1.Program n) throws Exception {
		// Init all the global tracking structures.
		funcMap = new HashMap<>();
		labelMap = new HashMap<>();
		Env env = new Env();
		memory = new ArrayList<>();
		retVal = new UndVal();

		// Variable to track lines of execution per func
		int count;

		for (IR1.Func f : n.funcs) {
			funcMap.put(f.gname.s, f);
			labelMap.put(f.gname.s, new LabMap());
			count = 0;

			for (IR1.Inst i : f.code) {
				if (i instanceof IR1.LabelDec) {
					LabMap funcLabel = labelMap.get(f.gname.s);
					// Insert the location in the LabMap for this function.
					funcLabel.put(((IR1.LabelDec) i).lab.name, count);
				}
				// Incremement every inst
				count++;
			}
		}
		execute(funcMap.get("_main"), env);
	}

	// Func ---
	//  Global gname;
	//  Id[] params;
	//  Id[] locals;
	//  Inst[] code;
	//
	// GUIDE:
	//  - Implement the fetch-execute loop.
	//  - The parameter 'env' is the function's initial Env, which
	//    contains its parameters' values.
	//
	static void execute(IR1.Func n, Env env) throws Exception {
		int idx = 0;
		while (idx < n.code.length) {
			int next = execute(n.code[idx], env);
			if (next == CONTINUE)
				idx++;
			else if (next == RETURN)
				break;
			else
				idx = next;
		}
	}

	// Dispatch execution to an individual Inst node.
	//
	static int execute(IR1.Inst n, Env env) throws Exception {
		if (n instanceof IR1.Binop) return execute((IR1.Binop) n, env);
		if (n instanceof IR1.Unop) return execute((IR1.Unop) n, env);
		if (n instanceof IR1.Move) return execute((IR1.Move) n, env);
		if (n instanceof IR1.Load) return execute((IR1.Load) n, env);
		if (n instanceof IR1.Store) return execute((IR1.Store) n, env);
		if (n instanceof IR1.Call) return execute((IR1.Call) n, env);
		if (n instanceof IR1.Return) return execute((IR1.Return) n, env);
		if (n instanceof IR1.Jump) return execute((IR1.Jump) n, env);
		if (n instanceof IR1.CJump) return execute((IR1.CJump) n, env);
		if (n instanceof IR1.LabelDec) return CONTINUE;
		throw new IntException("Unknown Inst: " + n);
	}

	//-----------------------------------------------------------------
	// Individual Instruction Nodes
	//-----------------------------------------------------------------
	//
	// - Each execute() routine returns CONTINUE, RETURN, or a new idx
	//   (target of jump).
	//
	// Binop ---
	//  BOP op;
	//  Dest dst;
	//  Src src1, src2;
	//
	// GUIDE:
	// 1. Evaluate the operands, then perform the operation.
	// 2. Update 'dst's entry in the Env with operation's result.
	//
	static int execute(IR1.Binop n, Env env) throws Exception {
		// Get the result of evalute from each side of the Binop
		Val leftVal = evaluate(n.src1, env);
		Val rightVal = evaluate(n.src2, env);
		Val result = null;

		// Execution sequence if Arithmetic Operand
		if (n.op instanceof IR1.AOP) {
			// If left and right are both Booleans
			if (leftVal instanceof BoolVal && rightVal instanceof BoolVal) {
				boolean leftBool = ((BoolVal) leftVal).b;
				boolean rightBool = ((BoolVal) rightVal).b;

				// Operator is &&
				if (n.op == IR1.AOP.AND) {
					result = new BoolVal(leftBool && rightBool);
				}
				// Operator is ||
				else {
					result = new BoolVal(leftBool || rightBool);
				}
			} // If left and right and int values
			else if (leftVal instanceof IntVal && rightVal instanceof IntVal) {
				int leftInt = ((IntVal) leftVal).i;
				int rightInt = ((IntVal) rightVal).i;

				// Switch based on what type of operand we see.
				switch ((IR1.AOP) n.op) {
					case ADD:
						result = new IntVal(leftInt + rightInt);
						break;
					case SUB:
						result = new IntVal(leftInt - rightInt);
						break;
					case MUL:
						result = new IntVal(leftInt * rightInt);
						break;
					case DIV:
						result = new IntVal(leftInt / rightInt);
						break;
				}
			}
		}	// Otherwise we must have a Relational Operand
		else if (n.op instanceof IR1.ROP) {
			// Check what type of values we have
			if (leftVal instanceof IntVal && rightVal instanceof IntVal) {
				int leftInt = ((IntVal) leftVal).i;
				int rightInt = ((IntVal) rightVal).i;

				switch ((IR1.ROP) n.op) {
					case GE:
						result = new BoolVal(leftInt >= rightInt);
						break;
					case GT:
						result = new BoolVal(leftInt > rightInt);
						break;
					case LE:
						result = new BoolVal(leftInt <= rightInt);
						break;
					case LT:
						result = new BoolVal(leftInt < rightInt);
						break;
					case EQ:
						result = new BoolVal(leftInt == rightInt);
						break;
					case NE:
						result = new BoolVal(leftInt != rightInt);
						break;
				}
			}
		}
		// Save value into the dst within the env
		env.put(n.dst.toString(), result);
		return CONTINUE;
	}


	// Unop ---
	//  UOP op;
	//  Dest dst;
	//  Src src;
	//
	// GUIDE:
	// 1. Evaluate the operand, then perform the operation.
	// 2. Update 'dst's entry in the Env with operation's result.
	//
	static int execute(IR1.Unop n, Env env) throws Exception {
		Val srcVal = evaluate(n.src, env);
		Val result = null;

		// Boolean
		if (srcVal instanceof BoolVal) {
			result = new BoolVal(!(((BoolVal) srcVal).b));
		} else { // Int
			result = new IntVal(-((IntVal) srcVal).i);
		}
		env.put(n.dst.toString(), result);
		return CONTINUE;
	}

	// Move ---
	//  Dest dst;
	//  Src src;
	//
	// GUIDE:
	//  Evaluate 'src', then update 'dst's entry in the Env.
	//
	static int execute(IR1.Move n, Env env) throws Exception {
		env.put(n.dst.toString(), evaluate(n.src, env));
		return CONTINUE;
	}

	// Load ---
	//  Dest dst;
	//  Addr addr;
	//
	// GUIDE:
	//  Evaluate 'addr' to a memory index, then retrieve the stored
	//  value from memory and update 'dst's entry in the Env.
	//
	static int execute(IR1.Load n, Env env) throws Exception {
		env.put(n.dst.toString(), memory.get(evaluate(n.addr, env)));
		return CONTINUE;
	}

	// Store ---
	//  Addr addr;
	//  Src src;
	//
	// GUIDE:
	// 1. Evaluate 'src' to a value.
	// 2. Evaluate 'addr' to a memory index, then store the value
	//    to the memory entry.
	//
	static int execute(IR1.Store n, Env env) throws Exception {
		memory.set(evaluate(n.addr, env), evaluate(n.src, env));
		return CONTINUE;
	}

	// CJump ---
	//  ROP op;
	//  Src src1, src2;
	//  Label lab;
	//
	// GUIDE:
	// 1. Evaluate the cond op.
	// 2. If cond is true, find and return the instruction index
	//    of the jump target label; otherwise return CONTINUE.
	//
	static int execute(IR1.CJump n, Env env) throws Exception {
		// Pretty much a duplicate of what I checked in BINOP
		//
		// Eval the src's so we can check types
		Val leftVal = evaluate(n.src1, env);
		Val rightVal = evaluate(n.src2, env);
		boolean result;

		// If Boolean
		if (leftVal instanceof BoolVal && rightVal instanceof BoolVal) {
			boolean leftBool = ((BoolVal) leftVal).b;
			boolean rightBool = ((BoolVal) rightVal).b;

			if (n.op == IR1.ROP.EQ) {
				result = (leftBool == rightBool);
			} else {
				result = (leftBool != rightBool);
			}
		}
		// Otherwise Int vals
		else if (leftVal instanceof IntVal && rightVal instanceof IntVal) {

			int leftInt = ((IntVal) leftVal).i;
			int rightInt = ((IntVal)rightVal).i;

			switch (n.op) {
				case LE:
					result = leftInt <= rightInt;
					break;
				case LT:
					result = leftInt < rightInt;
					break;
				case GE:
					result = leftInt >= rightInt;
					break;
				case GT:
					result = leftInt > rightInt;
					break;
				case EQ:
					result = leftInt == rightInt;
					break;
				case NE:
					result = leftInt != rightInt;
					break;
				// IntelliJ really wanted a default case here.
				default:
					throw new Exception("Apparently we didn't get a valid operand.");
			}
		}
		// Needed an else for IntelliJ to stop complaining at me.
		else {
			throw new Exception("Something went terribly wrong");
		}

		// If the conditional requirement is TRUE then we have to look
		// up the location of the jump target
		if (result) {
			// I have no idea how to get the function name so just iterate.
			for (LabMap i : labelMap.values()) {
				if(i.containsKey(n.lab.name)) {
					return i.get(n.lab.name);
				}
			}
		}
		// If the condition isnt met just roll through.
		return CONTINUE;
	}

	// Jump ---
	//  Label lab;
	//
	// GUIDE:
	//  Find and return the instruction index of the jump target label.
	//
	static int execute(IR1.Jump n, Env env) throws Exception {
		// Same as above, just brute force find the labmap
		for (LabMap i : labelMap.values()) {
			if(i.containsKey(n.lab.name)) {
				return i.get(n.lab.name);
			}
		}
		return RETURN;
	}


	// Call ---
	//  Global gname;
	//  Src[] args;
	//  Dest rdst;
	//
	// GUIDE:
	// 1. Evaluate the arguments to values.
	// 2. Create a new Env for the callee; pair function's parameter
	//    names with arguments' values, and add them to the new Env.
	// 3. Find callee's Func node and switch to execute it.
	// 4. If 'rdst' is not null, update its entry in the Env with
	//    the return value (should be avaiable in variable 'retVal').
	//
	static int execute(IR1.Call n, Env env) throws Exception {
		// Three cases to check based on pre defined functions in pdf
		// malloc, printInt, and printStr
		//
		// Malloc routine
		//
		if(n.gname.s.equals("_malloc")) {
			// Get current end point in arraylist
			int pos = memory.size();
			// Pull the size we need to malloc
			int memSize = ((IntVal) evaluate(n.args[0], env)).i;
			// Dump undefined values into memory for that object.
			// to represent allocation
			for(int i=0; i < memSize; i++) {
				memory.add(new UndVal());
			}
			// Save the location in memory to the destination
			env.put(n.rdst.toString(), new IntVal(pos));
		//
		// PrintInt routine
		//
		} else if (n.gname.s.equals("_printInt")) {
			Val val = evaluate(n.args[0], env);
			System.out.println("" + val);
		//
		// PrintStr routine
		//
		} else if (n.gname.s.equals("_printStr")) {
			Val val = evaluate(n.args[0], env);
			System.out.println("" + val);
		//
		// Some other Function has been called
		//
		} else {
			// Get func info
			IR1.Func func = funcMap.get(n.gname.s);
			// Create a new env for the function
			Env funcEnv = new Env();
			int count = 0;
			// Assume the params and args match up
			for(IR1.Id p: func.params) {
				funcEnv.put("" + p, evaluate(n.args[count], env));
				count++;
			}
			// Execute that
			execute(func, funcEnv);
			// Save return value into dst
			env.put(n.rdst.toString(), retVal);
		}
		return CONTINUE;
	}


	// Return ---
	//  Src val;
	//
	// GUIDE:
	//  If 'val' is not null, set it to the variable 'retVal'.
	//
	static int execute(IR1.Return n, Env env) throws Exception {
		if (n.val != null)
			retVal = evaluate(n.val, env);
		return RETURN;
	}

	//-----------------------------------------------------------------
	// Address and Operand Nodes.
	//-----------------------------------------------------------------
	//
	// - Each has an evaluate() routine.
	//

	// Address ---
	//  Src base;
	//  int offset;
	//
	// GUIDE:
	// 1. Evaluate 'base' to an integer, then add 'offset' to it.
	// 2. Return the result (which should be an index to memory).
	//
	static int evaluate(IR1.Addr n, Env env) throws Exception {
		int loc = ((IntVal) evaluate(n.base, env)).i;
		return loc + n.offset;
	}

	// Src Nodes
	//  -> Temp | Id | IntLit | BooLit | StrLit
	//
	// GUIDE:
	//  In each case, the evaluate() routine returns a Val object.
	//  - For Temp and Id, look up their value from the Env, wrap
	//    it in a Val and return.
	//  - For the literals, wrap their value in a Val and return.
	//
	static Val evaluate(IR1.Src n, Env env) throws Exception {
		Val val = null;
		if (n instanceof IR1.Temp) {
			val = env.get(n.toString());
		}
		if (n instanceof IR1.Id) {
			val = env.get(n.toString());
		}
		if (n instanceof IR1.IntLit) val = new IntVal(((IR1.IntLit) n).i);
		if (n instanceof IR1.BoolLit) val = new BoolVal(((IR1.BoolLit) n).b);
		if (n instanceof IR1.StrLit) val = new StrVal(((IR1.StrLit) n).s);
		return val;
	}

	// Dst Nodes
	//  -> Temp | Id
	//
	// GUIDE:
	//  For both cases, look up their value from the Env, wrap it
	//  in a Val and return.
	//
	static Val evaluate(IR1.Dest n, Env env) throws Exception {
		Val val = null;

		if (n instanceof IR1.Id) {
			val = env.get(n.toString());
		}
		if (n instanceof IR1.Temp) {
			val = env.get(n.toString());
		}
		return val;
	}

}
