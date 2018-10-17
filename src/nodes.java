import java.util.ArrayList;
import soot.* ;
import soot.options.*;
//import soot.unit;
import soot.util.*;
import soot.toolkits.graph.*;
import soot.jimple.*;
import soot.jimple.Stmt;


public class nodes{
public String lineNumber;
public boolean isCondition ;
public ArrayList<Unit> lineUnits;

public nodes(String lineNumber){
    lineUnits= new ArrayList<Unit>();
    this.lineNumber=lineNumber;
}

public int getnoOfNodes(){
    return lineUnits.size();
}

}
