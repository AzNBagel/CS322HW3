// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
//---------------------------------------------------------------------------
// For CS322 W'16 (J. Li).
//

// IR1 interpreter.
//
//
package ir;

import java.util.*;
import java.io.*;

public class IR1Interp {

	static class IntException extends Exception {
		public IntException(String msg) {
			super(msg);
		}
	}

	// Value representation
	//
	abstract static class Val {
		static final UndVal Undefined = new UndVal();

		int asInt() throws Exception {
			throw new IntException("Integer value expected");
		}

		boolean asBool() throws Exception {
			throw new IntException("Boolean value expected");
		}
	}

	// -- integer values
	//
	static class IntVal extends Val {
		int i;

		IntVal(int i) {
			this.i = i;
		}

		int asInt() throws Exception {
			return i;
		}

		public String toString() {
			return "" + i;
		}
	}

	// -- boolean values
	//
	static class BoolVal extends Val {
		boolean b;

		BoolVal(boolean b) {
			this.b = b;
		}

		boolean asBool() throws Exception {
			return b;
		}

		public String toString() {
			return "" + b;
		}
	}

	// -- string values
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

	// -- a special "undefined" value
	//
	static class UndVal extends Val {
		public String toString() {
			return "UndVal";
		}
	}

	// Environment representation
	//
	static class Env {
		HashMap<String, Integer> labelMap;  // label-to-idx map
		HashMap<String, Val> varMap;        // var/temp-to-val map

		Env() {
			labelMap = new HashMap<String, Integer>();
			varMap = new HashMap<String, Val>();
		}

		public String toString() {
			return "Env: labels" + labelMap + " vars" + varMap;
		}
	}

	static HashMap<String, IR1.Func> funcMap;  // func table
	static ArrayList<Val> storage;    // heap memory
	static final int CONTINUE = -1;    // execution status
	static final int RETURN = -2;      // execution status
	static Val retVal;        // return value

	static boolean statFlag = false;    // for reporting statistics
	static int instCnt = 0;

	// The main method
	//
	public static void main(String[] args) throws Exception {
		if (args.length >= 1) {
			FileInputStream stream;
			if (args[0].equals("-v")) {
				stream = new FileInputStream(args[1]);
				statFlag = true;
			} else {
				stream = new FileInputStream(args[0]);
			}
			IR1.Program p = new ir.IR1Parser(stream).Program();
			stream.close();
			IR1Interp.execute(p);
		} else {
			System.out.println("You must provide an input file name.");
		}
	}

	static int storageAlloc(int size) {
		int loc = storage.size();
		for (int i = 0; i < size; i++)
			storage.add(Val.Undefined);
		return loc;
	}

	// Program ---
	// Func[] funcs;
	//
	public static void execute(IR1.Program n) throws Exception {
		funcMap = new HashMap<String, IR1.Func>();
		storage = new ArrayList<Val>();
		retVal = Val.Undefined;
		for (IR1.Func f : n.funcs)
			funcMap.put(f.gname.s, f);
		execute(funcMap.get("_main"), new Env());
		if (statFlag)
			System.out.println("# Total instructions executed: " + instCnt);
	}

	// Func ---
	// String name;
	// Id[] params;
	// Id[] locals;
	// Inst[] code;
	//
	static void execute(IR1.Func n, Env env) throws Exception {
		for (int i = 0; i < n.code.length; i++) {
			if (n.code[i] instanceof IR1.LabelDec)
				env.labelMap.put(((IR1.LabelDec) n.code[i]).lab.name, i);
		}
		// the fetch-execute loop
		//  each execute() call returns CONTINUE, RETURN,
		//  or a new idx (target of jump)
		int idx = 0;
		while (idx < n.code.length) {
			instCnt++;
			int next = execute(n.code[idx], env);
			if (next == CONTINUE)
				idx++;
			else if (next == RETURN)
				break;
			else
				idx = next;
		}
	}

	// INSTRUCTIONS

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

	// Binop ---
	//  BOP op;
	//  Dest dst;
	//  Src src1, src2;
	//
	static int execute(IR1.Binop n, Env env) throws Exception {
		Val lval = evaluate(n.src1, env);
		Val rval = evaluate(n.src2, env);
		Val res = null;
		if (lval instanceof IntVal && rval instanceof IntVal) {
			int l = lval.asInt();
			int r = rval.asInt();
			if (n.op instanceof IR1.AOP) {
				IR1.AOP op = (IR1.AOP) n.op;
				switch (op) {
					case ADD:
						res = new IntVal(l + r);
						break;
					case SUB:
						res = new IntVal(l - r);
						break;
					case MUL:
						res = new IntVal(l * r);
						break;
					case DIV:
						res = new IntVal(l / r);
						break;
					default:
						throw new IntException("Bad AOP in Binop: " + op);
				}
			} else if (n.op instanceof IR1.ROP) {
				IR1.ROP op = (IR1.ROP) n.op;
				switch (op) {
					case EQ:
						res = new BoolVal(l == r);
						break;
					case NE:
						res = new BoolVal(l != r);
						break;
					case LT:
						res = new BoolVal(l < r);
						break;
					case LE:
						res = new BoolVal(l <= r);
						break;
					case GT:
						res = new BoolVal(l > r);
						break;
					case GE:
						res = new BoolVal(l >= r);
						break;
					default:
						throw new IntException("Bad ROP in Binop: " + op);
				}
			}
		} else if (lval instanceof BoolVal && rval instanceof BoolVal) {
			boolean l = lval.asBool();
			boolean r = rval.asBool();
			if (n.op instanceof IR1.AOP) {
				IR1.AOP op = (IR1.AOP) n.op;
				switch (op) {
					case AND:
						res = new BoolVal(l && r);
						break;
					case OR:
						res = new BoolVal(l || r);
						break;
					default:
						throw new IntException("Logic OP expected in Binop: " + op);
				}
			} else {
				throw new IntException("AOP expected in Binop: " + n.op);
			}
		} else {
			throw new IntException("Bad operands in Binop: " + n);
		}
		env.varMap.put(n.dst.toString(), res);
		return CONTINUE;
	}

	// Unop ---
	//  UOP op;
	//  Dest dst;
	//  Src src;
	//
	static int execute(IR1.Unop n, Env env) throws Exception {
		Val val = evaluate(n.src, env);
		Val res;
		if (n.op == IR1.UOP.NEG)
			res = new IntVal(-val.asInt());
		else if (n.op == IR1.UOP.NOT)
			res = new BoolVal(!val.asBool());
		else
			throw new IntException("Wrong op in Unop inst: " + n.op);
		env.varMap.put(n.dst.toString(), res);
		return CONTINUE;
	}

	// Move ---
	//  Dest dst;
	//  Src src;
	//
	static int execute(IR1.Move n, Env env) throws Exception {
		Val val = evaluate(n.src, env);
		env.varMap.put(n.dst.toString(), val);
		return CONTINUE;
	}

	// Load ---
	//  Dest dst;
	//  Addr addr;
	//
	static int execute(IR1.Load n, Env env) throws Exception {
		int loc = evaluate(n.addr, env);
		Val val = storage.get(loc);
		if (val == null)
			throw new IntException("No value at storage location " + loc);
		env.varMap.put(n.dst.toString(), val);
		return CONTINUE;
	}

	// Store ---
	//  Addr addr;
	//  Src src;
	//
	static int execute(IR1.Store n, Env env) throws Exception {
		Val val = evaluate(n.src, env);
		int loc = evaluate(n.addr, env);
		storage.set(loc, val);
		return CONTINUE;
	}

	// CJump ---
	//  ROP op;
	//  Src src1, src2;
	//  Label lab;
	//
	static int execute(IR1.CJump n, Env env) throws Exception {
		boolean cond;
		Val lval = evaluate(n.src1, env);
		Val rval = evaluate(n.src2, env);
		if (lval instanceof IntVal && rval instanceof IntVal) {
			int l = lval.asInt();
			int r = rval.asInt();
			switch (n.op) {
				case EQ:
					cond = (l == r);
					break;
				case NE:
					cond = (l != r);
					break;
				case LT:
					cond = (l < r);
					break;
				case LE:
					cond = (l <= r);
					break;
				case GT:
					cond = (l > r);
					break;
				case GE:
					cond = (l >= r);
					break;
				default:
					throw new IntException("Wrong op in CJump: " + n.op);
			}
		} else if (lval instanceof BoolVal && rval instanceof BoolVal) {
			boolean l = lval.asBool();
			boolean r = rval.asBool();
			switch (n.op) {
				case EQ:
					cond = (l == r);
					break;
				case NE:
					cond = (l != r);
					break;
				default:
					throw new IntException("Wrong op in CJump: " + n.op);
			}
		} else {
			throw new IntException("Error in CJump: " + n);
		}
		if (cond)
			return env.labelMap.get(n.lab.name);
		else
			return CONTINUE;
	}

	// Jump ---
	//  Label lab;
	//
	static int execute(IR1.Jump n, Env env) throws Exception {
		return env.labelMap.get(n.lab.name);
	}

	// Call ---
	//  Global gname;
	//  Src[] args;
	//  Dest rdst;
	//
	static int execute(IR1.Call n, Env env) throws Exception {
		if (n.gname.s.equals("_printInt")) {
			assert (n.args != null && n.args.length == 1);
			Val val = evaluate(n.args[0], env);
			System.out.println("" + val);
		} else if (n.gname.s.equals("_printStr")) {
			if (n.args == null || n.args.length == 0) {
				System.out.println();
			} else {
				Val val = evaluate(n.args[0], env);
				System.out.println("" + val);
			}
		} else if (n.gname.s.equals("_malloc")) {
			assert (n.args != null);
			int size = evaluate(n.args[0], env).asInt();
			int loc = storageAlloc(size);
			env.varMap.put(n.rdst.toString(), new IntVal(loc));
		} else {
			IR1.Func func = funcMap.get(n.gname.s);
			Env newenv = new Env();
			for (int i = 0; i < func.params.length; i++) {
				String pname = "" + func.params[i];
				Val argval = evaluate(n.args[i], env);
				newenv.varMap.put(pname, argval);
			}
			execute(func, newenv);
			env.varMap.put(n.rdst.toString(), retVal);
		}
		return CONTINUE;
	}

	// Return ---
	//  Src val;
	//
	static int execute(IR1.Return n, Env env) throws Exception {
		if (n.val != null)
			retVal = evaluate(n.val, env);
		return RETURN;
	}

	// Address ---
	//  Src base;
	//  int offset;
	//
	static int evaluate(IR1.Addr n, Env env) throws Exception {
		int loc = evaluate(n.base, env).asInt();
		return loc + n.offset;
	}

	// OPERANDS

	static Val evaluate(IR1.Src n, Env env) throws Exception {
		Val val = null;
		if (n instanceof IR1.Temp
						|| n instanceof IR1.Id) val = env.varMap.get(n.toString());
		if (n instanceof IR1.IntLit) val = new IntVal(((IR1.IntLit) n).i);
		if (n instanceof IR1.BoolLit) val = new BoolVal(((IR1.BoolLit) n).b);
		if (n instanceof IR1.StrLit) val = new StrVal(((IR1.StrLit) n).s);
		if (val == null)
			throw new IntException("Src '" + n + "' has no value");
		return val;
	}

	static Val evaluate(IR1.Dest n, Env env) throws Exception {
		Val val = env.varMap.get(n.toString());
		if (val == null)
			throw new IntException("Dest '" + n + "' has no value");
		return val;
	}

}
