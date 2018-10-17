/*
Control flow graph builder for Java
 Ali Alotaibi
*/


import java.io.File;
import soot.*;
import soot.options.*;
import soot.tagkit.LineNumberTag;
import soot.tagkit.SourceLnPosTag;
import soot.util.*;
import java.util.SortedMap;
import java.util.ArrayList;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.Units;

import java.util.TreeMap;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.beans.Statement;
import java.io.*;

public class CFG {
	public static String dottyStart = "digraph control_flow_graph { node [shape = rectangle]; Entry Exit;     node [shape = circle];";
	public static String dottyClose = "}";
	public static ArrayList<Edge> edges = new ArrayList<Edge>();
	public static TreeMap <String, ArrayList<String>> edgesToRemove=new TreeMap<String, ArrayList<String>>();
    public static SortedMap<String, nodes> instructions = new TreeMap<String, nodes>();
    public static SortedMap<String, ArrayList<String>> existingedges = new TreeMap<String, ArrayList<String>>();
	public static TreeMap<String,Stmt> skippedJimbles= new TreeMap<String,Stmt>();
    static String outputGraphFile;
    public static String lastLine;
    public static  Chain<Unit> units;

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
		units = b.getUnits();
		nodes = null;
		TreeMap<String,Stmt> skippedJimbles= new TreeMap<String, Stmt>();
		Unit last=units.getLast();
		lastLine= Integer.toString(last.getJavaSourceStartLineNumber());
		mapJibmbleToLines(null, "Exit");
		for (Unit u : units) {
            Stmt currStatement = (Stmt) u;
            System.out.println( currStatement.getJavaSourceStartLineNumber()+ " : "+ currStatement );
            String line= getLineNumber(currStatement);
            //if this node is being identified before as one of the problematic jimble statements in terms of line number

                mapJibmbleToLines(currStatement,line);      
            }
		correctLineNumbers();
		for (Unit u : units) {
			System.out.println(getLineNumber(u) + " : " + u);
		}
			
		draw(units, instructions);
		System.out.println("Size of edges"+ edges.size());
		//removeExtaEdges();
		System.out.println("Size of extraa edges"+ edgesToRemove.size());
		try {
			OutputStream output = new FileOutputStream(outputGraphFile);
			generateDotty(output, edges);
			output.close();
		} catch (IOException e) {
			System.out.println("Error while writing dottyFile " + outputGraphFile );
			System.exit(1);
		}
		//printEdges();
	}
		
	
	private static void toRemoveEdge(String from, String to) {
		ArrayList<String> temp;
		if(!edgesToRemove.containsKey(from)) {
				 temp= new ArrayList<>();
				 edgesToRemove.put(from, temp);
			}
		
		//temp.add(to);
		edgesToRemove.get(from).add(to);
		removeExtaEdges();
		
	}

	private static void removeExtaEdges() {
		ArrayList<Edge> temp= new ArrayList<Edge>(edges);
		for (String from : edgesToRemove.keySet()) {
			for (String to : edgesToRemove.get(from)) {
				for (Edge edge : temp) {
					if (edge.from.lineNumber.equalsIgnoreCase(from) && edge.to.lineNumber.equalsIgnoreCase(to)) {
						
						System.out.println(edges.remove(edge)+" Remooooooooooo0000000000000000000000000000"+ from+" --> "+ to );
						
					}
					
				}
				
			}
		}
	}



	public static void draw(Chain<Unit> units, SortedMap<String, nodes> instructions2) {

		String label = null;
		Edge edge;
		for (String key : instructions2.keySet()) {
			if(key.equalsIgnoreCase("Exit")) {
				continue;
			}
			ArrayList<Unit> jimisntr = instructions2.get(key).lineUnits;
			Unit sw = jimisntr.get(jimisntr.size() - 1);
			System.err.println();
			System.err.println();
			System.err.println("---------------------------------------");
			System.err.println("-------------- "+getLineNumber(sw)+" ,  "+sw+" -------------------------");
			System.err.println("---------------------------------------");
			if(getLineNumber(sw).equalsIgnoreCase("5")) {
				System.err.println("Line 5:"+ sw);
				System.err.println("Succ of 5"+ units.getSuccOf(sw));
			}
			if (sw instanceof LookupSwitchStmt || sw instanceof TableSwitchStmt || sw instanceof ReturnStmt
					|| sw instanceof RetStmt || sw instanceof ReturnVoidStmt) {
				jimisntr.subList(0, jimisntr.size() - 1).clear();
			}
		
			// get List of Jimble Instructions that Correspond to that Source Code Line 
			boolean foundSkip;
			for (int z = 0; z < jimisntr.size(); z++) {
				Unit jimpUnit = jimisntr.get(z);
				 foundSkip=false;

				label = null;
				Stmt s = (Stmt) jimpUnit;

				// Check Return Statements
				if (  sw instanceof ReturnStmt
						|| sw instanceof RetStmt || sw instanceof ReturnVoidStmt) {
					edge=new Edge(instructions2.get(key), instructions.get("Exit"),null);
					addEdge(edge);
				}

				else if (s instanceof IfStmt) {
					IfStmt IfStmt = (IfStmt) s;
					System.err.println("if in line"+ s.getJavaSourceStartLineNumber());	
					System.out.println("Orig succ of if is "+ getLineNumber(units.getSuccOf(IfStmt) ));
					System.out.println("orig target of if is "+ getLineNumber(IfStmt.getTarget() ));
					Stmt ifSucc = (Stmt) units.getSuccOf(IfStmt);
					Stmt ifTarget = IfStmt.getTarget();
					label = IfStmt.getCondition().toString();
					Expr expr = (Expr) IfStmt.getCondition();

					if (expr instanceof BinopExpr) {
						BinopExpr binop = (BinopExpr) expr;
						label = binop.getSymbol().trim();
					}
					
					System.err.println("if target not modified " +IfStmt.getTarget().getJavaSourceStartLineNumber());
					System.err.println("if succ modified" +ifSucc.getJavaSourceStartLineNumber());

					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(ifSucc) ), "!"+label);
					addEdge(edge);
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(ifTarget) ), label);
					addEdge(edge);

				}

				else if (s instanceof GotoStmt) {
					GotoStmt go = (GotoStmt) s;
					Stmt goTarget = (Stmt) go.getTarget();
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(goTarget) ), label);
					addEdge(edge);

				}

				else if (s instanceof LookupSwitchStmt) {
					LookupSwitchStmt lookup = (LookupSwitchStmt) s;
                    Value val = lookup.getKey();
                    System.out.println("inside lookupswitch");
                    System.out.println(s.getJavaSourceStartLineNumber());
                    System.out.println("Val: "+ val.getType().toString());

					if (!val.getType().toString().equals("byte")) {
						System.err.println("inside byte lookup");

//						continue;
					}
					ArrayList<Unit> switchTargets;
					Unit defaultTarget;
					switchTargets = new ArrayList<Unit>(lookup.getTargets());
					defaultTarget = lookup.getDefaultTarget();
					ArrayList<Value> lookupValues = new ArrayList<Value>(lookup.getLookupValues());
                    int i = 0;
                   

					for (Unit u : switchTargets) {
					
						System.out.println("switch target:" + u.getJavaSourceStartLineNumber());
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(u) ), "=="+lookupValues.get(i++).toString());
						addEdge(edge);

					}
					if (defaultTarget != null) {
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(defaultTarget) ), "default");
						addEdge(edge);


					}

				}

				else if (s instanceof TableSwitchStmt) {
					 System.err.println("it is table switch");
					TableSwitchStmt table = (TableSwitchStmt) s;
                    Value val = table.getKey();

					if (!val.getType().toString().equals("byte")) {
						System.err.println("inside byte table");


					//	continue;
					}
					ArrayList<Unit> switchTargets;
					Unit defaultTarget;
					switchTargets = new ArrayList<Unit>(table.getTargets());
					defaultTarget = table.getDefaultTarget();
                    
                    int i= table.getLowIndex();
					for (Unit u : switchTargets) {

						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(u) ), "=="+i++);
						addEdge(edge);

					}
					if (defaultTarget != null) {
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(defaultTarget)),"default" );
						addEdge(edge);


					}



				}

				else if (units.getSuccOf(jimpUnit) == null) {
					edge = new Edge(instructions.get(key), instructions.get("Exit"),null );
					addEdge(edge);
				}

				else if (s instanceof ThrowStmt) {

					continue;
				}

				else {
					if(units.getSuccOf(jimpUnit)==null) {
						continue;
					}
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(units.getSuccOf(jimpUnit))),null );
					System.err.println("valled line "+ key +" "+s );
					addEdge(edge);


				}

			}

		}


	

	}

	private static void mapJibmbleToLines (Stmt statement, String line) {
		String jimbleLine = line;
		nodes nodes= new nodes(line);
		if (!instructions.containsKey(jimbleLine)) {
			nodes = new nodes(line);
			instructions.put(jimbleLine, nodes);

		}
		if(statement!=null) {
		if (statement.branches()) {
			nodes.isCondition = true;
		}}
		nodes = instructions.get(jimbleLine);
		nodes.lineUnits.add(statement);

	}
	

	
	
	public static void addEdge(Edge edge) {
		if(edge.from!=null && edge.to!=null) {
		if(!edge.from.lineNumber.equalsIgnoreCase(edge.to.lineNumber)&&!edges.contains(edge)) {
	 			edges.add(edge);}
	 	
	    String from=edge.from.lineNumber;
	    String to=edge.to.lineNumber;
	    String label=edge.label;
	
	
	System.out.println(from + " -> " + to+  "                      [label = \"" + label + "\"];\n");
		
	}
}
	public static void generateDotty(OutputStream output, ArrayList<Edge> cfg) throws IOException {

		OutputStreamWriter osw = new OutputStreamWriter(output);
		osw.write(dottyStart + "\n");
		 for (Edge edge : edges) {
			 	if(edge.from==null || edge.to==null) {
			 		continue;
			 	}
			 	
			    String from=edge.from.lineNumber;
			    String to=edge.to.lineNumber;
			    String label=edge.label;
			    if (label != null) {
			    	osw.write(from + " -> " + to+  " [label = \"" + label + "\"];\n");
			    }
			    else {
			    	osw.write(from + " -> " + to + "\n");
			    }
			if (from.equalsIgnoreCase(to)) {
				continue;
			}
			
			//System.out.println(from + " -> " + to+  " [label = \"" + label + "\"];\n");
				
			}

		osw.write(dottyClose + "\n");
		osw.flush();
		osw.close();

	}
	
	private static void correctLineNumbers() {
		for (Unit unit : units) {
			String key = getLineNumber(unit);
			if (unit instanceof IfStmt) {
				IfStmt IfStmt = (IfStmt) unit;
				Stmt ifSucc = (Stmt) units.getSuccOf(IfStmt);
				Stmt ifTarget = IfStmt.getTarget();
				if (getLineNumber(ifSucc).equalsIgnoreCase(lastLine) && ifSucc instanceof IfStmt) {
					System.err.println("inside LastLine" + getLineNumber(unit));
					instructions.get(lastLine).lineUnits.remove(ifSucc);
					instructions.get(key).lineUnits.add(ifSucc);
					IfStmt f = (IfStmt) ifSucc;
					editLineNumber(ifSucc, key);

				} else if (!getLineNumber(ifSucc).equalsIgnoreCase("Entry") && ifSucc instanceof IfStmt) {
					System.err.println("inside not ENtry" + getLineNumber(unit));
					int succLineNumber = Integer.parseInt(getLineNumber(ifSucc));
					int ifLineNumber = Integer.parseInt(key);
					if (ifLineNumber > succLineNumber) {
						instructions.get(getLineNumber(ifSucc)).lineUnits.remove(ifSucc);
						instructions.get(key).lineUnits.add(ifSucc);
						IfStmt tempif = (IfStmt) ifSucc;
						editLineNumber(ifSucc, key);

					}
				}
			}

		}
	}
	private static void editLineNumber(Unit s, String line) {
		LineNumberTag lnTag = (LineNumberTag) s.getTag("LineNumberTag");
		System.err.println("Changed...from" +getLineNumber(s));
		if (lnTag != null) {
			lnTag.setLineNumber(Integer.parseInt(line));
			System.err.println("to.. "+ line);
		}
	}
	private static String getLineNumber(Unit s) {
		 if(s==null) {
			 return "Exit";
			 }
		LineNumberTag lnTag = (LineNumberTag) s.getTag("LineNumberTag");
		if (lnTag != null){
			 return Integer.toString(lnTag.getLineNumber());}
		 return "Entry";
	}
}
