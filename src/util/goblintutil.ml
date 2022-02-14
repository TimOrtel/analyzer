(** Globally accessible flags and utility functions. *)

open Cil
open GobConfig


(** Outputs information about what the goblin is doing *)
(* let verbose = ref false *)

(** Files given as arguments. *)
let arg_files : string list ref = ref []

(** If this is true we output messages and collect accesses.
    This is set to true in control.ml before we verify the result (or already before solving if warn = 'early') *)
let should_warn = ref false

(** Whether signed overflow or underflow happened *)
let svcomp_may_overflow = ref false

(** hack to use a special integer to denote synchronized array-based locking *)
let inthack = Int64.of_int (-19012009) (* TODO do we still need this? *)

(** The file where everything is output *)
let out = ref stdout

(** Temp directory, set in maingoblint.ml, but used by the OSEK analysis. *)
let tempDirName = ref "goblint_temp"

(** Command for assigning an id to a varinfo. All varinfos directly created by Goblint should be modified by this method *)
let create_var (var: varinfo) =
  (* TODO Hack: this offset should preempt conflicts with ids generated by CIL *)
  let start_id = 10_000_000_000 in
  let hash = Hashtbl.hash { var with vid = 0 } in
  let hash = if hash < start_id then hash + start_id else hash in
  { var with vid = hash }

(* Type invariant variables. *)
let type_inv_tbl = Hashtbl.create 13
let type_inv (c:compinfo) : varinfo =
  try Hashtbl.find type_inv_tbl c.ckey
  with Not_found ->
    let i = create_var (makeGlobalVar ("{struct "^c.cname^"}") (TComp (c,[]))) in
    Hashtbl.add type_inv_tbl c.ckey i;
    i

let is_blessed (t:typ): varinfo option =
  let me_gusta x = List.mem x (get_string_list "exp.unique") in
  match unrollType t with
  | TComp (ci,_) when me_gusta ci.cname -> Some (type_inv ci)
  | _ -> (None : varinfo option)


(** A hack to see if we are currently doing global inits *)
let global_initialization = ref false

(** Another hack to see if earlyglobs is enabled *)
let earlyglobs = ref false

(** Whether currently in postsolver evaluations (e.g. verify, warn) *)
let postsolving = ref false

(* None if verification is disabled, Some true if verification succeeded, Some false if verification failed *)
let verified : bool option ref = ref None

let escape = XmlUtil.escape (* TODO: inline everywhere *)


(** Creates a directory and returns the absolute path **)
let create_dir name =
  let dirName = if Filename.is_relative name then Filename.concat (Unix.getcwd ()) name else name in
  (* The directory should be writable to group and user *)
  let dirPerm = 0o770 in
  let _ =
    try
      Unix.mkdir dirName dirPerm
    with Unix.Unix_error(err, ctx1, ctx) as ex ->
      (* We can discared the EEXIST, we are happy to use the existing directory *)
      if err != Unix.EEXIST then begin
        (* Hopefully will be friendly enough :) *)
        print_endline ("Error, " ^ (Unix.error_message err));
        raise ex
      end
  in
  dirName

(** Remove directory and its content, as "rm -rf" would do. *)
let rm_rf path =
  let rec f path =
    if Sys.is_directory path then begin
      let files = Array.map (Filename.concat path) (Sys.readdir path) in
      Array.iter f files;
      Unix.rmdir path
    end else
      Sys.remove path
  in
  f path


exception Timeout

let timeout = Timeout.timeout

let seconds_of_duration_string =
  let unit = function
    | "" | "s" -> 1
    | "m" -> 60
    | "h" -> 60 * 60
    | s -> failwith ("Unkown duration unit " ^ s ^ ". Supported units are h, m, s.")
  in
  let int_rest f s = Scanf.sscanf s "%u%s" f in
  let split s = BatString.(head s 1, tail s 1) in
  let rec f i s =
    let u, r = split s in (* unit, rest *)
    i * (unit u) + if r = "" then 0 else int_rest f r
  in
  int_rest f

let vars = ref 0
let evals = ref 0

(* print GC statistics; taken from Cil.Stats.print which also includes timing; there's also Gc.print_stat, but it's in words instead of MB and more info than we want (also slower than quick_stat since it goes through the heap) *)
let print_gc_quick_stat chn =
  let gc = Gc.quick_stat () in
  let printM (w: float) : string =
    let coeff = float_of_int (Sys.word_size / 8) in
    Printf.sprintf "%.2fMB" (w *. coeff /. 1000000.0)
  in
  Printf.fprintf chn
    "Memory statistics: total=%s, max=%s, minor=%s, major=%s, promoted=%s\n    minor collections=%d  major collections=%d compactions=%d\n"
    (printM (gc.Gc.minor_words +. gc.Gc.major_words
              -. gc.Gc.promoted_words))
    (printM (float_of_int gc.Gc.top_heap_words))
    (printM gc.Gc.minor_words)
    (printM gc.Gc.major_words)
    (printM gc.Gc.promoted_words)
    gc.Gc.minor_collections
    gc.Gc.major_collections
    gc.Gc.compactions;
  gc

let scrambled = try Sys.getenv "scrambled" = "true" with Not_found -> false
(* typedef struct {
   PROCESS_NAME_TYPE      NAME;
   SYSTEM_ADDRESS_TYPE    ENTRY_POINT;
   STACK_SIZE_TYPE        STACK_SIZE;
   PRIORITY_TYPE          BASE_PRIORITY;
   SYSTEM_TIME_TYPE       PERIOD;
   SYSTEM_TIME_TYPE       TIME_CAPACITY;
   DEADLINE_TYPE          DEADLINE;
   }                        PROCESS_ATTRIBUTE_TYPE; *)
let arinc_name          = if scrambled then "M161" else "NAME"
let arinc_entry_point   = if scrambled then "M162" else "ENTRY_POINT"
let arinc_base_priority = if scrambled then "M164" else "BASE_PRIORITY"
let arinc_period        = if scrambled then "M165" else "PERIOD"
let arinc_time_capacity = if scrambled then "M166" else "TIME_CAPACITY"

let exe_dir = Filename.dirname Sys.executable_name
let command = String.concat " " (Array.to_list Sys.argv)

(* https://ocaml.org/api/Sys.html#2_SignalnumbersforthestandardPOSIXsignals *)
(* https://ocaml.github.io/ocamlunix/signals.html *)
let signal_of_string = let open Sys in function
  | "sigint"  -> sigint  (* Ctrl+C Interactive interrupt *)
  | "sigtstp" -> sigtstp (* Ctrl+Z Interactive stop *)
  | "sigquit" -> sigquit (* Ctrl+\ Interactive termination *)
  | "sigalrm" -> sigalrm (* Timeout *)
  | "sigkill" -> sigkill (* Termination (cannot be ignored) *)
  | "sigsegv" -> sigsegv (* Invalid memory reference, https://github.com/goblint/analyzer/issues/206 *)
  | "sigterm" -> sigterm (* Termination *)
  | "sigusr1" -> sigusr1 (* Application-defined signal 1 *)
  | "sigusr2" -> sigusr2 (* Application-defined signal 2 *)
  | "sigstop" -> sigstop (* Stop *)
  | "sigprof" -> sigprof (* Profiling interrupt *)
  | "sigxcpu" -> sigxcpu (* Timeout in cpu time *)
  | s -> failwith ("Unhandled signal " ^ s)

let self_signal signal = Unix.kill (Unix.getpid ()) signal

let rec for_all_in_range (a, b) f =
  let module BI = IntOps.BigIntOps in
  if BI.compare a b > 0
  then true
  else f a && (for_all_in_range (BI.add a (BI.one), b) f)

let dummy_obj = Obj.repr ()
