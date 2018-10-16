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
//            for(String key: skippedJimbles.keySet()) {
//            	Stmt statementToSkip= skippedJimbles.get(key);
//            	if(currStatement.equals(statementToSkip)) {
//            		 line=key;
//            	}
//            }	
            	
                mapJibmbleToLines(currStatement,line);
                
                
            }
			

		draw(units, instructions);
		System.out.println("Size of edges"+ edges.size());
		removeExtaEdges();
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

		// Add first Edge from Entry
	//	addEdge("Entry", Integer.toString(instructions2.firstKey()), null);

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
				//skipp skipped jimples ( like last stat in if block after fixing if else in same line problem
//				for (String string : skippedJimbles.keySet()) {
//					if(string.equalsIgnoreCase(key)&& skippedJimbles.get(key).equals((Stmt)jimpUnit)) {
//						 foundSkip=true;
//					}
//				}
//				if(foundSkip) {
//					continue;
//				}
				// for(Unit jimpUnit:jimisntr){
				label = null;
				Stmt s = (Stmt) jimpUnit;

				// Check Return Statements
				if (  sw instanceof ReturnStmt
						|| sw instanceof RetStmt || sw instanceof ReturnVoidStmt) {
					//addEdge(key, "Exit", null);
					edge=new Edge(instructions2.get(key), instructions.get("Exit"),null);
					addEdge(edge);
				}

				else if (s instanceof IfStmt) {
					boolean modified=false;
					IfStmt IfStmt = (IfStmt) s;
					System.err.println("if in line"+ s.getJavaSourceStartLineNumber());	
					System.out.println("Orig succ of go is "+ getLineNumber(units.getSuccOf(IfStmt) ));
					System.out.println("orig target of go is "+ getLineNumber(IfStmt.getTarget() ));
					Stmt ifSucc = (Stmt) units.getSuccOf(IfStmt);
					Stmt ifTarget = IfStmt.getTarget();
					label = IfStmt.getCondition().toString();
					Expr expr = (Expr) IfStmt.getCondition();

					if (expr instanceof BinopExpr) {
						BinopExpr binop = (BinopExpr) expr;
						label = binop.getSymbol().trim();
					}
					if(getLineNumber(IfStmt).equalsIgnoreCase(getLineNumber(ifTarget))){
						System.out.println("It is insssside first if");
						if(ifTarget instanceof IfStmt) {
							System.out.println("It is insssside second if");
							
							String targetsucc=getLineNumber(units.getSuccOf(ifTarget));
							int intsuccNumber=Integer.parseInt(targetsucc);
							String number=Integer.toString(intsuccNumber-1);
							Unit test=instructions.get(number).lineUnits.get(0);
							System.out.println("test: "+ number+" "+ test);
							if(test instanceof GotoStmt) {
								System.out.println("ALLLLLLLI it is instance of go line "+getLineNumber(test));
								GotoStmt g= (GotoStmt)test;
								System.out.println("heeeeey succ of go is "+ getLineNumber(units.getSuccOf(g) ));
								System.out.println("heeeeey target of go is "+ getLineNumber(g.getTarget() ));

								if(getLineNumber(units.getSuccOf(g)).equalsIgnoreCase(key)) {
									System.out.println("Problematttttttttic::: ( } else if ) found");
									//System.err.println("remvoe of go "+ units.remove(g));
									
									/*remove go to and add it to last statement of if..
									add else to in correct line istead of goto
									*/
									instructions.get(getLineNumber(g)).lineUnits.remove(g);
									int goToIfElseLine=Integer.parseInt(getLineNumber(g));
									 String lastLineIfBlock=Integer.toString(goToIfElseLine-1);
									Unit unit2=units.getPredOf(g);
									lastLineIfBlock=getLineNumber(unit2);
									System.out.println(lastLineIfBlock+ " ::::::::::::::::: "+unit2 );
									//skippedJimbles.put(lastLineIfBlock, (Stmt) unit2);
									toRemoveEdge(lastLineIfBlock,getLineNumber(g));
								//	unit2.redirectJumpsToThisTo(arg0);
									 //add goto to last statement of the if block
									if(instructions.get(lastLineIfBlock)!=null)
									instructions.get(lastLineIfBlock).lineUnits.add(g);
									//addNodetoLine(g,lastLineIfBlock);
									//instructions.get(getLineNumber(ifSucc)).lineUnits.add(g);
									instructions.get(getLineNumber(g)).lineUnits.add(ifTarget);
									
									instructions.get(getLineNumber(IfStmt)).lineUnits.remove(ifTarget);
									edge=new Edge(instructions.get(key), instructions.get(getLineNumber(g)),  "!"+label);
									addEdge(edge);
									edge = new Edge(instructions.get(key), instructions.get(getLineNumber(ifSucc) ), label);
									addEdge(edge);
									System.out.println("if succ " + getLineNumber(ifSucc));
									System.out.println("succ of  succ " +getLineNumber(units.getSuccOf(ifSucc))+" "+ units.getSuccOf(ifSucc));
									modified=true;
									
								}
							}
						}
					} 
				
					 if(getLineNumber(ifSucc).equalsIgnoreCase(lastLine)&& ifSucc instanceof IfStmt){
							System.out.println("fffffffffff inside exit of if " );
						instructions.get(lastLine).lineUnits.remove(ifSucc);
						instructions.get(key).lineUnits.add(ifSucc);
						IfStmt f=(IfStmt)ifSucc;
						System.err.println("if Exit target " +getLineNumber(f.getTarget()));
						System.err.println("if Exit succ " +getLineNumber(units.getSuccOf(f)));
						System.err.println("if succ " +ifSucc.getJavaSourceStartLineNumber());
						toRemoveEdge(key,lastLine);
						modified=true;
						
							
						}else if(!getLineNumber(ifSucc).equalsIgnoreCase("Entry") && ifSucc instanceof IfStmt) {
							System.out.println("fffffffffff inside entry of if "+modified);
						int succLineNumber= Integer.parseInt(getLineNumber(ifSucc));
						int ifLineNumber= Integer.parseInt(key);
						if(ifLineNumber>succLineNumber) {
							instructions.get(getLineNumber(ifSucc)).lineUnits.remove(ifSucc);
							instructions.get(key).lineUnits.add(ifSucc);
							toRemoveEdge(key,getLineNumber(ifSucc));
							modified=true;

						}
						}					
 
					if(!modified) {
//					if(ifTarget.getJavaSourceStartLineNumber()> ifSucc.getJavaSourceStartLineNumber()){
//						if(ifSucc instanceof IfStmt){
//							System.err.println("WORRRRKED");
//							skippedJimbles.put(key,ifSucc);
//							instructions.get(getLineNumber(ifSucc)).lineUnits.remove(ifSucc);
//							mapJibmbleToLines(ifSucc, key);
//							ifSucc=(Stmt) units.getSuccOf(ifSucc);
//							
//							
//						}
//						
//					}
					
					System.err.println("if target not modified " +IfStmt.getTarget().getJavaSourceStartLineNumber());
					System.err.println("if succ modified" +ifSucc.getJavaSourceStartLineNumber());
//					label = IfStmt.getCondition().toString();
//					 expr = (Expr) IfStmt.getCondition();
//					if (expr instanceof BinopExpr) {
//						BinopExpr binop = (BinopExpr) expr;
//						label = binop.getSymbol().trim();
//					}
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(ifSucc) ), "!"+label);
//					addEdge(Integer.toString(key), Integer.toString(ifSucc.getJavaSourceStartLineNumber()),
//							"!" + label);
					addEdge(edge);
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(ifTarget) ), label);
					addEdge(edge);
					//addEdge(Integer.toString(key), Integer.toString(ifTarget.getJavaSourceStartLineNumber()), label);

				}
				}

				else if (s instanceof GotoStmt) {
					GotoStmt go = (GotoStmt) s;
					Stmt goTarget = (Stmt) go.getTarget();
//					if( goTarget.getJavaSourceStartLineNumber()!=units.getSuccOf(go).getJavaSourceStartLineNumber()){
//						if(go.getJavaSourceStartLineNumber()> units.getSuccOf(go).getJavaSourceStartLineNumber()){
//						goTarget.removeAllTags();
//						System.err.println("Remooved"+ goTarget.getJavaSourceStartLineNumber());
//					}
//					}
				//	System.out.println(go.getJavaSourceStartColumnNumber()+ goTarget.getJavaSourceStartColumnNumber());
//					System.out.println(" it is go from " +go.getJavaSourceStartLineNumber()+  " to line: "+ goTarget.getJavaSourceStartLineNumber());
//					System.out.println(" it is go frpm " +go.getJavaSourceStartLineNumber()+ " next "+ units.getSuccOf(go).getJavaSourceStartLineNumber());
//					if(getLineNumber(go).equalsIgnoreCase(getLineNumber(goTarget))){
//					if(!getLineNumber(goTarget).equalsIgnoreCase("exit") ){
//						int goLine=Integer.parseInt(getLineNumber(go));
//						int targetLine=Integer.parseInt(getLineNumber(goTarget));
//						if(goLine>targetLine) {
//							System.out.println("Ingore go before else bracekt");
//							continue;
//						}
//					}
//					}
					edge = new Edge(instructions.get(key), instructions.get(getLineNumber(goTarget) ), label);
					addEdge(edge);
					//addEdge(Integer.toString(key), Integer.toString(goTarget.getJavaSourceStartLineNumber()), null);

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
						
                      //  StringConstant IntConstant = (StringConstant) 	lookupValues.get(i);
                        //System.out.println("StringConstant "+ IntConstant+ " u.getValue():" );
						System.out.println("switch target:" + u.getJavaSourceStartLineNumber());
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(u) ), "=="+lookupValues.get(i++).toString());
						addEdge(edge);
//						addEdge(Integer.toString(key), Integer.toString(u.getJavaSourceStartLineNumber()),
//								"=="+lookupValues.get(i++).toString());
					}
					if (defaultTarget != null) {
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(defaultTarget) ), "default");
						addEdge(edge);
//						addEdge(Integer.toString(key), Integer.toString(defaultTarget.getJavaSourceStartLineNumber()),
//								"default");

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
					//ArrayList<Value> tableValues = new ArrayList<Value>(table.getLookupValues());
                    
                    int i= table.getLowIndex();
					for (Unit u : switchTargets) {
                      //  StringConstant IntConstant = (StringConstant) 	lookupValues.get(i);
                        //System.out.println("StringConstant "+ IntConstant+ " u.getValue():" );
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(u) ), "=="+i++);
						addEdge(edge);
//						addEdge(Integer.toString(key), Integer.toString(u.getJavaSourceStartLineNumber()),
//								"=="+i++);
					}
					if (defaultTarget != null) {
						edge = new Edge(instructions.get(key), instructions.get(getLineNumber(defaultTarget)),"default" );
						addEdge(edge);
//						addEdge(Integer.toString(key), Integer.toString(defaultTarget.getJavaSourceStartLineNumber()),
//								"default");

					}



				}

				else if (units.getSuccOf(jimpUnit) == null) {
					edge = new Edge(instructions.get(key), instructions.get("Exit"),null );
					addEdge(edge);
//					addEdge(Integer.toString(key), "Exit", null);
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
//					addEdge(Integer.toString(key),
//							Integer.toString(units.getSuccOf(jimpUnit).getJavaSourceStartLineNumber()), null);

				}

			}

		}


	

	}





	private static void addNodetoLine(GotoStmt g, String lastLineIfBlock) {
		
		instructions.get(lastLineIfBlock).lineUnits.add(g);
		
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
	

//	public static void addEdge(String from, String to, String label) {
//        ArrayList<String> existTo=existingedges.get(from);
//        boolean result=false;
//        if(existTo==null){
//            existTo= new ArrayList<String>();
//        }
//        else{
//        for (String var : existTo) {
//            if(to.equalsIgnoreCase(var))
//            result=true;   
//          }
//        }       
//		if (!from.equalsIgnoreCase(to) && !result) {
//			//System.out.println(from + " -> " + to);
//			ed = new Edge(from + " -> " + to, label);
//            edges.add(ed);
//            existTo.add(to);
//            existingedges.put(from,existTo);
//		}
//	}

	
	
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
	
	private static String getLineNumber(Unit s) {

		// LineNumberTag lnTag = (LineNumberTag) s.getTag("LineNumberTag");
		// if (lnTag != null)
		// return Integer.toString(lnTag.getLineNumber());
		// SourceLnPosTag tag = (SourceLnPosTag) s.getTag("SourceLnPosTag");
		// if (tag != null)
		// return Integer.toString(tag.startLn());
		//
		//
		// return Integer.toString(-1);

		// String line = Integer.toString(s.getJavaSourceStartLineNumber());
		if(s==null) {
			return "Exit";
		}
		String line = Integer.toString(s.getJavaSourceStartLineNumber());
		if (line.equalsIgnoreCase("-1")) {
			line = "Entry";
		}
//		if (line.equalsIgnoreCase(lastLine)) {
//			line = "Exit";
//		}
	
		return line;
	}
}
