import java.util.ArrayList;
import soot.* ;
import soot.options.*;
//import soot.unit;
import soot.util.*;
import soot.toolkits.graph.*;
import soot.jimple.*;
import soot.jimple.Stmt;



public class nodes{
public boolean isCondition ;
public ArrayList<Unit> lineUnits;

public nodes(){
    lineUnits= new ArrayList<Unit>();
}

public int getnoOfNodes(){
    return lineUnits.size();
}

}
