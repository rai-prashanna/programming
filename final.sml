signature GRAPH = 
sig 
  type ''a T
  val empty: ''a T
  val add_vertex: ''a T -> ''a  -> ''a T
  val add_edge: ''a T -> ''a -> ''a ->''a T
  val vertices: ''a T -> ''a list
  val neighbors: ''a T -> ''a -> ''a list
  val displayGraph: string T -> string
  val connected_components: ''a T -> ''a T list 
end;


structure Graph : GRAPH =
struct
datatype ''a component = Void | Point of (''a ) | Connected of (''a component * (''a component) list) list | Edge of (''a component * ''a component) | Path of (''a list);
type ''a T = ''a component 
val empty = Void
fun add_vertex Void (a) = Point(a)
  | add_vertex (Point(a)) (b)=Connected([(Point(a),[]),(Point(b),[])])
  | add_vertex (Connected(xs)) (b)=Connected([(Point(b),[])] @ xs)

fun addComponent (Connected([])) (Connected([])) = Connected([]) | addComponent (Connected([])) (Connected(x::xs)) = Connected(x::xs) 
  | addComponent (Connected(xs)) (Connected(ys)) = Connected(xs@ys)

fun add_edge Void point1 point2 = (Connected([]))
  | add_edge (Point(a)) point1 point2 = (Connected([]))
  | add_edge (Connected([])) point1 point2 =(Connected([]))
  | add_edge (Connected(x::xs): ''a component) (point1:''a) (point2:''a) =  
  let 
    val (point , edges) = x
    val (Point(value)) = point
    val pointOne =Point(point1)
    val pointTwo =Point(point2)
    in 
      if (value=point1 orelse value=point2) then addComponent (Connected([(point,[Edge(Point(point1),Point(point2))]@edges)])) (add_edge (Connected(xs)) point1 point2) 
    else (addComponent (Connected([x])) (add_edge (Connected(xs)) point1 point2))
  end

fun getPointsExcluding ([]) element= [] 
| getPointsExcluding ((Edge (Point(value1), Point(value2)))::xs) element= if (value1 <> element) then [value1] @ getPointsExcluding (xs) element else [value2] @ getPointsExcluding (xs) element


fun vertices Void = []
| vertices (Point(a)) = [a]
| vertices (Connected([])) =[]
| vertices (Connected(x::xs)) =
  let
    val (point , edges) = x
    val (Point(value)) = point
    in
    [value] @ (vertices(Connected(xs)))
end

fun neighbors Void element = []
| neighbors (Point(a)) element = []
| neighbors (Connected([])) element = []
| neighbors (Connected((Point(a),[])::xs)) element = neighbors (Connected(xs)) element
| neighbors (Connected((Point(a),ys)::xs)) element = if (a=element) then getPointsExcluding (ys) element else neighbors (Connected(xs)) element

fun removeSimilarEdges ((Edge (Point(value11), Point(value12)))) ((Edge (Point(value21), Point(value22))))= if ((value11=value22) orelse (value11=value21)) then ((Edge (Point(value11), Point(value12)))::[]) 
else if ((value12=value22) orelse (value12=value21)) then ((Edge (Point(value11), Point(value12)))::[]) else ((Edge (Point(value11), Point(value12))))::((Edge (Point(value21), Point(value22))))::[]

fun getAllEdges (Connected([])) =[]
  | getAllEdges (Connected((Point(a),[])::xs)) = getAllEdges(Connected(xs))
  | getAllEdges (Connected((Point(a),ys)::xs)) = ys@getAllEdges(Connected(xs))

fun filteredges [] = []
| filteredges (x::y::xs) = (removeSimilarEdges x y) @ filteredges xs

fun getVerticesInString (Connected([])) = " "
| getVerticesInString (Connected(x::xs)) =
let
   val (y::ys) = vertices (Connected(x::xs)) 
 in
 "\n"^"   "^y^";"^"   "^"\n"^"   "^getVerticesInString(Connected(xs))  
 end

fun getedgesinstring [] = ""
| getedgesinstring (((Edge (Point(value1), Point(value2))))::xs) = "\n"^"   "^value1^"  --  "^value2^";"^"  "^"\n"^"   "^getedgesinstring(xs)


fun displayGraph (Connected([])) = (" ")
| displayGraph (Connected(x::xs)) = 
  let
    val edgeslist = getAllEdges (Connected(x::xs))
    val edgeslist' = filteredges edgeslist
    val edgesString = getedgesinstring edgeslist'
    val verticesString = getVerticesInString (Connected(x::xs))  
  in
    ("\n"^"graph {"^verticesString^edgesString^"\n"^"}") 
  end

fun removeDuplicate [] = []
  | removeDuplicate ((l as x::xs):''a list) =
      let fun remove (x,[]) = []
            | remove (x,l as y::ys) = if x = y
                                      then remove(x,ys)
                                      else y::remove(x,ys)
      in
        x::removeDuplicate(remove(x,xs))
      end

fun mergeCommonList ([]) ([]) = [] | 
  mergeCommonList (list1) ([]) = [] |
  mergeCommonList ((list1):''a list) ((list2):''a list) = let 
    fun helper' (x::xs) ([]) = helper' (xs) (list2) | 
      helper' ([]) ([]) =[] | 
      helper' (x::xs) (y::ys) = if (x=y) then removeDuplicate (list1@list2) else helper' (x::xs) (ys)
  in
    helper' (list1) (list2)
  end 

fun mergePath' ([[]]) ([[]]) = [] | 
  mergePath' (list1) ([[]]) =  [] | 
  mergePath' ([]::xs) ([]::ys) =  mergePath' (xs) (ys) |
mergePath' ((x11::x12::x1s):''a list list) ((list2):''a list list) = let
  val intermediateresult1 = [mergeCommonList (x11) (x12)]
  val intermediateresult = intermediateresult1@x1s
in
  intermediateresult1  
end


fun conv ([]) = [] | conv (x::xs) = Path(x)::conv(xs); 


fun getPathFromPoints (Connected([])) point = [] | 
  getPathFromPoints (Connected((Point(a),[])::xs)) point = 
  if (a=point) then [] else getPathFromPoints (Connected(xs)) point | 
    getPathFromPoints (Connected((Point(a),e::es)::xs)) point = 
    if (a=point) then let
      val Edge((Point(p1) ,Point(p2))) = e
      fun helper' (a) ([]) = [] |
      helper' (a) (x::xs) =
      let
        val Edge((Point(ep1) ,Point(ep2))) = x
       in 
        if ((a=ep1) orelse (a=ep2)) then [ep1,ep2]@helper' a xs else helper' a xs
       end 
    in
      helper' (point) (e::es)
    end  
    else getPathFromPoints (Connected(xs)) point


fun getConnectedPaths' (Connected([])) copy = [] | 
getConnectedPaths' (Connected((Point(a),[])::xs)) copy = (getPathFromPoints (copy) a) :: (getConnectedPaths' (Connected(xs)) copy) | 
getConnectedPaths' ((Connected(x::xs))) (copy) = let
  val (Point(b),e::es) = x
in
  getPathFromPoints (copy) (b) :: getConnectedPaths' (Connected(xs)) copy  
end


fun connected_components ((Connected(x::xs))) = let
  val unfilteredConectedPaths = getConnectedPaths' ((Connected(x::xs))) ((Connected(x::xs)))
  val intermediateresult = mergePath' unfilteredConectedPaths unfilteredConectedPaths
in conv (intermediateresult) end

end;


functor GRAPHAlGORITHMS(G: GRAPH) =
struct
  fun dot graph = G.displayGraph (graph)
  fun connected_components graph = G.connected_components (graph)  
end;

structure graphalgo = GRAPHAlGORITHMS(Graph);
graphalgo.dot g1;
graphalgo.dot g2;
graphalgo.dot g3;




graphalgo.connected_components g1;
graphalgo.connected_components g2;
graphalgo.connected_components g3;
