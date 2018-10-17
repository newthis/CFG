public class Edge{
public nodes from;
public nodes to;
public String edge;
public String label;



//public Edge(String edge, String label ){
//    this.edge=edge;
//    this.label=label;
//}

public Edge(nodes from, nodes to, String label ){
    this.from=from;
    this.to=to;
    this.label=label;
}
	@Override
    public boolean equals(Object obj) {
 		boolean result=false;
 		 if (obj == null) {
             return false;
         }
            Edge edge  = (Edge) obj;
        //    System.err.println("inside equals: ");
         //   System.err.println("        "+ this.local.getName()+" ,"+varObj.local.getName()+" ,"+ this.defLine+" ,"+varObj.defLine);
            if(this.from.lineNumber.equalsIgnoreCase(edge.from.lineNumber) && this.to.lineNumber.equalsIgnoreCase(edge.to.lineNumber)) {
            if(this.edge!=null && this.edge!=null){
            	if(this.edge.equalsIgnoreCase(edge.label))
            	result= true;}}
      //   System.out.println(result);
            	return result;
            
        
        }
 	@Override
    public int hashCode() {
 		
 		int hash=31;
 		hash= hash*from.lineNumber.hashCode()+ to.lineNumber.hashCode()+ from.lineUnits.get(0).toString().hashCode();
        return hash;
          
    }
}
