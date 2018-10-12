/*
Control flow graph builder for Java
 Ali Alotaibi
*/


import java.io.File;
import soot.*;
import soot.options.*;
import soot.util.*;
import java.util.SortedMap;
import java.util.ArrayList;
import soot.jimple.*;
import soot.jimple.Stmt;
import java.util.TreeMap;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.*;

public class CFG {
	public static String dottyStart = "digraph control_flow_graph { node [shape = rectangle]; Entry Exit;     node [shape = circle];";
	public static String dottyClose = "}";
	public static ArrayList<Edge> edges = new ArrayList<Edge>();
    public static SortedMap<Integer, nodes> instructions = new TreeMap<Integer, nodes>();
    public static SortedMap<String, ArrayList<String>> existingedges = new TreeMap<String, ArrayList<String>>();

    static String outputGraphFile;

	public static Edge ed;

	public static void main(String[] args) {

        if ( args.length != 3 ) {
			System.err.println( "AError! You should enter 3 arguments" );
			System.exit( 1 );
        }
        for (String var : args) {
            System.out.println("Argument: "+var);
            
        }
        String className = args[0];
        outputGraphFile = args[1];
        String classDir=args[2];        
        String  sootClassPath = Scene.v().getSootClassPath() + File.pathSeparator + classDir;

		// SortedMap<Integer, nodes> instructions = new TreeMap<Integer, nodes>();
		nodes nodes;
      
        
		// String className = "example1";
		// String classDir = "/mnt/c/Users/aliso/OneDrive/PhD USC/Courses/CSCI610/Assignments/bin";
        // String sootClassPath = Scene.v().getSootClassPath() + File.pathSeparator + classDir;
		// outputGraphFile="cfgOutpot.dotty";
		
		Scene.v().setSootClassPath(sootClassPath);
		Options.v().set_keep_line_number(true);
		// Keep line numbers
		SootClass sc = Scene.v().loadClassAndSupport(className);
		// get class referecne and store it in sc
		Scene.v().loadNecessaryClasses();
		sc.setApplicationClass();
		SootMethod sm = sc.getMethodByName("main");
		if (sm == null) {
			System.err.println("Error, No main method found");
			System.exit(0);
		}
		Body b = sm.retrieveActiveBody();
		Chain<Unit> units = b.getUnits();

		int instLine = -1;
		nodes = null;
		for (Unit u : units) {
            Stmt statement = (Stmt) u;

            if(u instanceof LookupSwitchStmt){
                LookupSwitchStmt lu=(LookupSwitchStmt)u;
                ArrayList<Value> lookupValues = new ArrayList<Value>(lu.getLookupValues());

                for (Value var : lookupValues) {
                    if(var instanceof IntConstant){
                        IntConstant IntConstant = (IntConstant) var;
                        System.out.println("IntConstant "+ IntConstant );

                    }
                    else if(var instanceof StringConstant){
                        StringConstant StringConstant = (StringConstant) var;
                        System.out.println("StringConstant "+ StringConstant );}

                    }
                
                
               // StringConstant IntConstant = (StringConstant) 	lookupValues.get(i);
              //  System.out.println("StringConstant "+ IntConstant+ " u.getValue():" + u.getValue().toString());
            }
			instLine = statement.getJavaSourceStartLineNumber();
			if (instLine < 0) {
				continue;
			}

			if (!instructions.containsKey(instLine)) {
				nodes = new nodes();
				instructions.put(instLine, nodes);

			}
			if (statement.branches()) {
				nodes.isCondition = true;
			}
			nodes = instructions.get(instLine);
			nodes.lineUnits.add(statement);

		}

		draw(units, instructions);

	}



	public static void draw(Chain<Unit> units, SortedMap<Integer, nodes> instruc) {

		// Add first Edge from Entry
		addEdge("Entry", Integer.toString(instruc.firstKey()), null);

		String label = null;
		for (int key : instruc.keySet()) {

			ArrayList<Unit> jimisntr = instruc.get(key).lineUnits;
			Unit sw = jimisntr.get(jimisntr.size() - 1);
			if (sw instanceof LookupSwitchStmt || sw instanceof TableSwitchStmt || sw instanceof ReturnStmt
					|| sw instanceof RetStmt || sw instanceof ReturnVoidStmt) {
				jimisntr.subList(0, jimisntr.size() - 1).clear();
			}
			// get List of Jimble Instructions that Correspond to that Source Code Line 
			for (int z = 0; z < jimisntr.size(); z++) {
				Unit jimpUnit = jimisntr.get(z);

				// for(Unit jimpUnit:jimisntr){
				label = null;
				Stmt s = (Stmt) jimpUnit;

				// Check Return Statements
				if (jimpUnit instanceof ReturnStmt || jimpUnit instanceof RetStmt
						|| jimpUnit instanceof ReturnVoidStmt) {
					addEdge(Integer.toString(key), "Exit", null);

				}

				else if (s instanceof IfStmt) {
					IfStmt IfStmt = (IfStmt) s;
					Stmt ifSucc = (Stmt) units.getSuccOf(IfStmt);
					Stmt ifTargert = IfStmt.getTarget();

					label = IfStmt.getCondition().toString();
					Expr expr = (Expr) IfStmt.getCondition();

					if (expr instanceof BinopExpr) {
						BinopExpr binop = (BinopExpr) expr;
						label = binop.getSymbol().trim();
					}

					addEdge(Integer.toString(key), Integer.toString(ifSucc.getJavaSourceStartLineNumber()),
							"!" + label);
					addEdge(Integer.toString(key), Integer.toString(ifTargert.getJavaSourceStartLineNumber()), label);

				}

				else if (s instanceof GotoStmt) {
					GotoStmt go = (GotoStmt) s;
					Stmt goTarget = (Stmt) go.getTarget();
					addEdge(Integer.toString(key), Integer.toString(goTarget.getJavaSourceStartLineNumber()), null);

				}

				else if (s instanceof LookupSwitchStmt) {
					LookupSwitchStmt lookup = (LookupSwitchStmt) s;
                    Value val = lookup.getKey();

					if (!val.getType().toString().equals("byte")) {

						continue;
					}
					ArrayList<Unit> switchTargets;
					Unit defaultTarget;
					switchTargets = new ArrayList<Unit>(lookup.getTargets());
					defaultTarget = lookup.getDefaultTarget();
					ArrayList<Value> lookupValues = new ArrayList<Value>(lookup.getLookupValues());
                    int i = 0;
                   

					for (Unit u : switchTargets) {
                      //  StringConstant IntConstant = (StringConstant) 	lookupValues.get(i);
                        //System.out.println("StringConstant "+ IntConstant+ " u.getValue():" );
						addEdge(Integer.toString(key), Integer.toString(u.getJavaSourceStartLineNumber()),
								"=="+lookupValues.get(i++).toString());
					}
					if (defaultTarget != null) {
						addEdge(Integer.toString(key), Integer.toString(defaultTarget.getJavaSourceStartLineNumber()),
								"default");

					}

				}

				else if (s instanceof TableSwitchStmt) {
                    
					TableSwitchStmt table = (TableSwitchStmt) s;
                    Value val = table.getKey();

					if (!val.getType().toString().equals("byte")) {


						continue;
					}
					ArrayList<Unit> switchTargets;
					Unit defaultTarget;
					switchTargets = new ArrayList<Unit>(table.getTargets());
					defaultTarget = table.getDefaultTarget();
					//ArrayList<Value> tableValues = new ArrayList<Value>(table.getLookupValues());
                    
                    int i= table.getLowIndex();
					for (Unit u : switchTargets) {
                      //  StringConstant IntConstant = (StringConstant) 	lookupValues.get(i);
                        //System.out.println("StringConstant "+ IntConstant+ " u.getValue():" );
						addEdge(Integer.toString(key), Integer.toString(u.getJavaSourceStartLineNumber()),
								"=="+i++);
					}
					if (defaultTarget != null) {
						addEdge(Integer.toString(key), Integer.toString(defaultTarget.getJavaSourceStartLineNumber()),
								"default");

					}



				}

				else if (units.getSuccOf(jimpUnit) == null) {
					addEdge(Integer.toString(key), "Exit", null);
				}

				else if (s instanceof ThrowStmt) {

					continue;
				}

				else {

					addEdge(Integer.toString(key),
							Integer.toString(units.getSuccOf(jimpUnit).getJavaSourceStartLineNumber()), null);

				}

			}

		}


		try {
			OutputStream output = new FileOutputStream(outputGraphFile);
			generateDotty(output, edges);
			output.close();
		} catch (IOException e) {
			System.out.println("Error while writing dottyFile " + outputGraphFile );
			System.exit(1);
		}

	}

	public static void addEdge(String from, String to, String label) {
        ArrayList<String> existTo=existingedges.get(from);
        boolean result=false;
        if(existTo==null){
            existTo= new ArrayList<String>();
        }
        else{
        for (String var : existTo) {
            if(to.equalsIgnoreCase(var))
            result=true;   
          }
        }       
		if (!from.equalsIgnoreCase(to) && !result) {
			System.out.println(from + " -> " + to);
			ed = new Edge(from + " -> " + to, label);
            edges.add(ed);
            existTo.add(to);
            existingedges.put(from,existTo);
		}
	}

	public static void generateDotty(OutputStream output, ArrayList<Edge> cfg) throws IOException {

		OutputStreamWriter osw = new OutputStreamWriter(output);
		osw.write(dottyStart + "\n");
		for (Edge e : cfg) {
			if (e.label != null) {
				osw.write(e.edge + " [label = \"" + e.label + "\"];\n");
			} else {
				osw.write(e.edge + "\n");
			}
		}

		osw.write(dottyClose + "\n");
		osw.flush();
		osw.close();

	}
}
