open MyCFG
open Queue
open Cil
include CompareAST

let eq_node (x, fun1) (y, fun2) =
  let empty_context: context = ([], []) in
  match x,y with
  | Statement s1, Statement s2 -> eq_stmt ~cfg_comp:true (s1, fun1) (s2, fun2) empty_context
  | Function f1, Function f2 -> eq_varinfo f1.svar f2.svar empty_context
  | FunctionEntry f1, FunctionEntry f2 -> eq_varinfo f1.svar f2.svar empty_context
  | _ -> false

(* TODO: compare ASMs properly instead of simply always assuming that they are not the same *)
let eq_edge x y = 
  let empty_context: context = ([], []) in
  match x, y with
  | Assign (lv1, rv1), Assign (lv2, rv2) -> eq_lval lv1 lv2 empty_context && eq_exp rv1 rv2 empty_context
  | Proc (None,f1,ars1), Proc (None,f2,ars2) -> eq_exp f1 f2 empty_context && GobList.equal (eq_exp2 empty_context) ars1 ars2 
  | Proc (Some r1,f1,ars1), Proc (Some r2,f2,ars2) ->
    eq_lval r1 r2 empty_context && eq_exp f1 f2 empty_context && GobList.equal (eq_exp2 empty_context) ars1 ars2
  | Entry f1, Entry f2 -> eq_varinfo f1.svar f2.svar empty_context
  | Ret (None,fd1), Ret (None,fd2) -> eq_varinfo fd1.svar fd2.svar empty_context
  | Ret (Some r1,fd1), Ret (Some r2,fd2) -> eq_exp r1 r2 empty_context && eq_varinfo fd1.svar fd2.svar empty_context
  | Test (p1,b1), Test (p2,b2) -> eq_exp p1 p2 empty_context && b1 = b2
  | ASM _, ASM _ -> false
  | Skip, Skip -> true
  | VDecl v1, VDecl v2 -> eq_varinfo v1 v2 empty_context
  | SelfLoop, SelfLoop -> true
  | _ -> false

(* The order of the edges in the list is relevant. Therefore compare them one to one without sorting first *)
let eq_edge_list xs ys = GobList.equal eq_edge xs ys

let to_edge_list ls = List.map (fun (loc, edge) -> edge) ls

module NH = Hashtbl.Make(Node)
type biDirectionNodeMap = {node1to2: node NH.t; node2to1: node NH.t}

(* This function compares two CFGs by doing a breadth-first search on the old CFG. Matching node tuples are stored in same,
 * nodes from the old CFG for which no matching node can be found are added to diff. For each matching node tuple
 * (fromNode1, fromNode2) found, one iterates over the successors of fromNode1 from the old CFG and checks for a matching node
 * in the succesors of fromNode2 in the new CFG. Matching node tuples are added to the waitingList to repeat the matching
 * process on their successors. If a node from the old CFG can not be matched, it is added to diff and no further
 * comparison is done for its successors. The two function entry nodes make up the tuple to start the comparison from. *)
let compareCfgs (module CfgOld : CfgForward) (module CfgNew : CfgForward) fun1 fun2 =
  let diff = NH.create 113 in
  let same = {node1to2=NH.create 113; node2to1=NH.create 113} in
  let waitingList : (node * node) t = Queue.create () in

  let rec compareNext () =
    if Queue.is_empty waitingList then ()
    else
      let fromNode1, fromNode2 = Queue.take waitingList in
      let outList1 = CfgOld.next fromNode1 in
      let outList2 = CfgNew.next fromNode2 in

      (* Find a matching edge and successor node for (edgeList1, toNode1) in the list of successors of fromNode2.
       * If successful, add the matching node tuple to same, else add toNode1 to the differing nodes. *)
      let findMatch (edgeList1, toNode1) =
        let rec aux remSuc = match remSuc with
          | [] -> NH.replace diff toNode1 ()
          | (locEdgeList2, toNode2)::remSuc' ->
            let edgeList2 = to_edge_list locEdgeList2 in
            (* TODO: don't allow pseudo return node to be equal to normal return node, could make function unchanged, but have different sallstmts *)
            if eq_node (toNode1, fun1) (toNode2, fun2) && eq_edge_list edgeList1 edgeList2 then
              begin
                match NH.find_opt same.node1to2 toNode1 with
                | Some n2 -> if not (Node.equal n2 toNode2) then NH.replace diff toNode1 ()
                | None -> NH.replace same.node1to2 toNode1 toNode2; NH.replace same.node2to1 toNode2 toNode1; Queue.add (toNode1, toNode2) waitingList
              end
            else aux remSuc' in
        aux outList2 in
      (* For a toNode1 from the list of successors of fromNode1, check whether it might have duplicate matches.
       * In that case declare toNode1 as differing node. Else, try finding a match in the list of successors
       * of fromNode2 in the new CFG using findMatch. *)
      let iterOuts (locEdgeList1, toNode1) =
        let edgeList1 = to_edge_list locEdgeList1 in
        (* Differentiate between a possibly duplicate Test(1,false) edge and a single occurence. In the first
         * case the edge is directly added to the diff set to avoid undetected ambiguities during the recursive
         * call. *)
        let testFalseEdge edge = match edge with
          | Test (p,b) -> p = Cil.one && b = false
          | _ -> false in
        let posAmbigEdge edgeList = let findTestFalseEdge (ll,_) = testFalseEdge (snd (List.hd ll)) in
          let numDuplicates l = List.length (List.find_all findTestFalseEdge l) in
          testFalseEdge (List.hd edgeList) && (numDuplicates outList1 > 1 || numDuplicates outList2 > 1) in
        if posAmbigEdge edgeList1 then NH.replace diff toNode1 ()
        else findMatch (edgeList1, toNode1) in
      List.iter iterOuts outList1; compareNext () in

  let entryNode1, entryNode2 = (FunctionEntry fun1, FunctionEntry fun2) in
  NH.replace same.node1to2 entryNode1 entryNode2; NH.replace same.node2to1 entryNode2 entryNode1;
  Queue.push (entryNode1,entryNode2) waitingList; compareNext (); (same, diff)

(* This is the second phase of the CFG comparison of functions. It removes the nodes from the matching node set 'same'
 * that have an incoming backedge in the new CFG that can be reached from a differing new node. This is important to
 * recognize new dependencies between unknowns that are not contained in the infl from the previous run. *)
let reexamine f1 f2 (same : biDirectionNodeMap) (diffNodes1 : unit NH.t) (module CfgOld : CfgForward) (module CfgNew : CfgBidir) =
  let rec repeat () =
    let check_all_nodes_in_same ps n =
      match List.find_opt (fun p -> not (NH.mem same.node2to1 p)) ps with
      | None -> true
      | Some p ->
        begin
          let n1 = NH.find same.node2to1 n in
          NH.replace diffNodes1 n1 ();
          NH.remove same.node1to2 n1; NH.remove same.node2to1 n;
          false
        end in
    let cond n2 = Node.equal n2 (FunctionEntry f2) || check_all_nodes_in_same (List.map snd (CfgNew.prev n2)) n2 in
    let forall = NH.fold (fun n2 n1 acc -> acc && cond n2) same.node2to1 true in
    if not forall then repeat () in
  repeat ();
  NH.to_seq same.node1to2, NH.to_seq_keys diffNodes1

let compareFun (module CfgOld : CfgForward) (module CfgNew : CfgBidir) fun1 fun2 =
  let same, diff = Stats.time "compare-phase1" (fun () -> compareCfgs (module CfgOld) (module CfgNew) fun1 fun2) () in
  let unchanged, diffNodes1 = Stats.time "compare-phase2" (fun () -> reexamine fun1 fun2 same diff (module CfgOld) (module CfgNew)) () in
  List.of_seq unchanged, List.of_seq diffNodes1
