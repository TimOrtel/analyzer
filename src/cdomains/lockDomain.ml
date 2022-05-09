module Addr = ValueDomain.Addr
module Offs = ValueDomain.Offs
module Equ = MusteqDomain.Equ
module Exp = Exp.Exp
module IdxDom = ValueDomain.IndexDomain

open Cil

module Mutexes = SetDomain.ToppedSet (Addr) (struct let topname = "All mutexes" end) (* TODO HoareDomain? *)
module Simple = Lattice.Reverse (Mutexes)
module Priorities = IntDomain.Lifted

module OsekGlob =
struct
  module Var = Basetype.Variables
  module Val = Priorities
end

module Glob =
struct
  module Var = Basetype.Variables
  module Val = Simple
end

module Lockset =
struct

  (* true means exclusive lock and false represents reader lock*)
  module RW   = IntDomain.Booleans

  (* pair Addr and RW; also change pretty printing*)
  module Lock =
  struct
    include Printable.Prod (Addr) (RW)

    let pretty () (a, write) =
      if write then
        Addr.pretty () a
      else
        Pretty.dprintf "read lock %a" Addr.pretty a

    include Printable.SimplePretty (
      struct
        type nonrec t = t
        let pretty = pretty
      end
      )
  end

  (* TODO: use SetDomain.Reverse *)
  module ReverseAddrSet = SetDomain.ToppedSet (Lock)
      (struct let topname = "All mutexes" end)

  module AddrSet = Lattice.Reverse (ReverseAddrSet)

  include AddrSet

  let rec may_be_same_offset of1 of2 =
    match of1, of2 with
    | `NoOffset , `NoOffset -> true
    | `Field (x1,y1) , `Field (x2,y2) -> CilType.Compinfo.equal x1.fcomp x2.fcomp && may_be_same_offset y1 y2 (* TODO: why not fieldinfo equal? *)
    | `Index (x1,y1) , `Index (x2,y2)
      -> (not (IdxDom.is_int x1) || not (IdxDom.is_int x2))
         || IdxDom.equal x1 x2 && may_be_same_offset y1 y2
    | _ -> false

  let add (addr,rw) set =
    match (Addr.to_var_offset addr) with
    | Some (_,x) when Offs.is_definite x -> ReverseAddrSet.add (addr,rw) set
    | _ -> set

  let remove (addr,rw) set =
    let collect_diff_varinfo_with (vi,os) (addr,rw) =
      match (Addr.to_var_offset addr) with
      | Some (v,o) when CilType.Varinfo.equal vi v -> not (may_be_same_offset o os)
      | Some (v,o) -> true
      | None -> false
    in
    match (Addr.to_var_offset addr) with
    | Some (_,x) when Offs.is_definite x -> ReverseAddrSet.remove (addr,rw) set
    | Some x -> ReverseAddrSet.filter (collect_diff_varinfo_with x) set
    | _   -> AddrSet.top ()

  let empty = ReverseAddrSet.empty
  let is_empty = ReverseAddrSet.is_empty

  let map = ReverseAddrSet.map
  let filter = ReverseAddrSet.filter
  let fold = ReverseAddrSet.fold
  let singleton = ReverseAddrSet.singleton
  let mem = ReverseAddrSet.mem
  let exists = ReverseAddrSet.exists

  let export_locks ls =
    let f (x,_) set = Mutexes.add x set in
    fold f ls (Mutexes.empty ())
end

module MayLockset =
struct
  include Lockset
  let leq x y = leq y x
  let join = Lockset.meet
  let meet = Lockset.join
  let top = Lockset.bot
  let bot = Lockset.top
end

module Symbolic =
struct
  (* TODO: use SetDomain.Reverse *)
  module S = SetDomain.ToppedSet (Exp) (struct let topname = "All mutexes" end)
  include Lattice.Reverse (S)

  let empty = S.empty
  let is_empty = S.is_empty

  let rec eq_set (ask: Queries.ask) e =
    S.union
      (match ask.f (Queries.EqualSet e) with
       | es when not (Queries.ES.is_bot es) ->
         Queries.ES.fold S.add es (S.empty ())
       | _ -> S.empty ())
      (match e with
       | SizeOf _
       | SizeOfE _
       | SizeOfStr _
       | AlignOf _
       | Const _
       | AlignOfE _
       | UnOp _
       | BinOp _ -> S.empty ()
       | AddrOf  (Var _,_)
       | StartOf (Var _,_)
       | Lval    (Var _,_) -> S.singleton e
       | AddrOf  (Mem e,ofs) -> S.map (fun e -> AddrOf  (Mem e,ofs)) (eq_set ask e)
       | StartOf (Mem e,ofs) -> S.map (fun e -> StartOf (Mem e,ofs)) (eq_set ask e)
       | Lval    (Mem e,ofs) -> S.map (fun e -> Lval    (Mem e,ofs)) (eq_set ask e)
       | CastE (_,e)           -> eq_set ask e
       | Question _ -> failwith "Logical operations should be compiled away by CIL."
       | _ -> failwith "Unmatched pattern.")

  let add (ask: Queries.ask) e st =
    let no_casts = S.map Expcompare.stripCastsDeepForPtrArith (eq_set ask e) in
    let addrs = S.filter (function AddrOf _ -> true | _ -> false) no_casts in
    S.union addrs st
  let remove ask e st =
    (* TODO: Removing based on must-equality sets is not sound! *)
    let no_casts = S.map Expcompare.stripCastsDeepForPtrArith (eq_set ask e) in
    let addrs = S.filter (function AddrOf _ -> true | _ -> false) no_casts in
    S.diff st addrs
  let remove_var v st = S.filter (fun x -> not (Exp.contains_var v x)) st

  let kill_lval (host,offset) st =
    let rec last_field os ls =
      match os with
      | NoOffset -> ls
      | Index (i,o) -> last_field o None
      | Field (f,o) -> last_field o (Some f)
    in
    match last_field offset None with
    | Some f -> S.filter (fun x -> not (Exp.contains_field f x)) st
    | None ->
      match host with
      | Var v -> remove_var v st
      | Mem (Lval (Var v, NoOffset)) -> remove_var v st
      | Mem _ ->  top ()

  let elements = S.elements
  let choose = S.choose
  let filter = S.filter
  let union = S.union
  let fold = S.fold

end
