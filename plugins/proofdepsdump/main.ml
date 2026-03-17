module Lsp = Fleche_lsp
open Fleche

module JLang = Lsp.JLang
module CoqJ = Lsp.JCoq
module SSet = Set.Make (String)
module SMap = Map.Make (String)

module Dep = struct
  module Location = struct
    type t = { range : JLang.Range.t } [@@deriving to_yojson]
  end

  type t =
    { name : string
    ; logical_path : string
    ; physical_path : string option
    ; locations : Location.t list
    }
  [@@deriving to_yojson]
end

module NotationRef = struct
  type t =
    { name : string
    ; logical_path : string
    ; locations : Dep.Location.t list
    }
  [@@deriving to_yojson]
end

module GoalHyp = struct
  type t =
    { names : string list
    ; def : string option
    ; ty : string
    }
  [@@deriving to_yojson]
end

module Goal = struct
  type t =
    { evar : int
    ; name : string option
    ; hyps : GoalHyp.t list
    ; ty : string
    }
  [@@deriving to_yojson]
end

module GoalState = struct
  type t =
    { goals : Goal.t list
    ; stack : (Goal.t list * Goal.t list) list
    ; bullet : string option
    ; shelf : Goal.t list
    ; given_up : Goal.t list
    }
  [@@deriving to_yojson]
end

module Step = struct
  type t =
    { index : int
    ; range : JLang.Range.t
    ; raw : string
    ; tactic_tags : string list
    ; notations : NotationRef.t list
    ; deps : Dep.t list
    ; goals_after : GoalState.t option
    }
  [@@deriving to_yojson]
end

module Proof = struct
  type t =
    { proof_id : int
    ; name : string
    ; start_range : JLang.Range.t
    ; statement : string
    ; statement_notations : NotationRef.t list
    ; axioms : Dep.t list
    ; initial_goals : GoalState.t option
    ; steps : Step.t list
    }
  [@@deriving to_yojson]
end

type dump =
  { astdump_jsonl : Yojson.Safe.t list
  ; proofs : Proof.t list
  }

let proofs_to_yojson { proofs; _ } =
  let proofs = `List (List.map Proof.to_yojson proofs) in
  `Assoc [ ("proofs", proofs) ]

let ast_to_yojson { astdump_jsonl; _ } =
  `Assoc [ ("astdump_jsonl", `List astdump_jsonl) ]

let state_before ~(doc : Doc.t) (node : Doc.Node.t) =
  Stdlib.Option.fold ~none:doc.root ~some:Doc.Node.state node.prev

let proof_name_of_state st =
  Coq.State.lemmas ~st |> Option.map Coq.State.Proof.name

let result_of_execution (v : ('a, 'l) Coq.Protect.E.t) : 'a option =
  match v.r with
  | Coq.Protect.R.Completed (Ok x) -> Some x
  | Coq.Protect.R.Completed (Error _)
  | Coq.Protect.R.Interrupted -> None

let value_for_key key json =
  match json with
  | `Assoc fields -> List.assoc_opt key fields
  | `List fields ->
    List.find_map
      (function
        | `List [ `String k; value ] when String.equal k key -> Some value
        | _ -> None)
      fields
  | _ -> None

let unwrap_v json = match value_for_key "v" json with Some v -> v | None -> json

let rec unwrap_singleton_list = function
  | `List [ x ] -> unwrap_singleton_list x
  | x -> x

let id_of_json = function
  | `List [ `String "Id"; `String id ] -> Some id
  | _ -> None

let dirpath_of_json = function
  | `List [ `String "DirPath"; `List ids ] ->
    List.filter_map id_of_json ids |> List.rev
  | _ -> []

let qualid_string_of_json json =
  match unwrap_v json with
  | `List (`String "Ser_Qualid" :: dp :: id :: _) -> (
    match id_of_json id with
    | None -> None
    | Some id -> (
      match dirpath_of_json dp with
      | [] -> Some id
      | dp -> Some (String.concat "." (dp @ [ id ]))))
  | _ -> None

let basename_of_qualid qid =
  match String.rindex_opt qid '.' with
  | None -> qid
  | Some i -> String.sub qid (i + 1) (String.length qid - i - 1)

let int_of_json = function
  | `Int i -> Some i
  | `Intlit s
  | `String s -> int_of_string_opt s
  | _ -> None

let loc_range_of_json ~lines json =
  let json = unwrap_singleton_list json in
  let get_int key = Stdlib.Option.bind (value_for_key key json) int_of_json in
  match
    ( get_int "line_nb"
    , get_int "line_nb_last"
    , get_int "bol_pos"
    , get_int "bol_pos_last"
    , get_int "bp"
    , get_int "ep" )
  with
  | Some line_nb, Some line_nb_last, Some bol_pos, Some bol_pos_last, Some bp, Some ep ->
    let loc =
      Loc.
        { fname = ToplevelInput
        ; line_nb
        ; bol_pos
        ; line_nb_last
        ; bol_pos_last
        ; bp
        ; ep
        }
    in
    Some (Coq.Utils.to_range ~lines loc)
  | _ -> None

type qualid_occurrence =
  { qid : string
  ; range : JLang.Range.t option
  }

let qualid_occurrence_of_json ~lines json =
  match qualid_string_of_json json with
  | None -> None
  | Some qid ->
    let range =
      Stdlib.Option.bind
        (value_for_key "loc" json)
        (loc_range_of_json ~lines)
    in
    Some { qid; range }

let rec qualid_occurrences ~lines acc json =
  let acc =
    match qualid_occurrence_of_json ~lines json with
    | None -> acc
    | Some occ -> occ :: acc
  in
  let json = unwrap_v json in
  let acc =
    match json with
    | `List (`String "CRef" :: qid_json :: _) -> (
      match qualid_occurrence_of_json ~lines qid_json with
      | None -> acc
      | Some occ -> occ :: acc)
    | _ -> acc
  in
  match json with
  | `Assoc fields ->
    List.fold_left
      (fun acc (_, value) -> qualid_occurrences ~lines acc value)
      acc fields
  | `List values -> List.fold_left (qualid_occurrences ~lines) acc values
  | _ -> acc

let starts_with ~prefix s =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix

let set_of_list xs =
  List.fold_left (fun acc x -> SSet.add x acc) SSet.empty xs

let tac_wrappers =
  set_of_list
    [ "TacAtom"
    ; "TacThen"
    ; "TacDispatch"
    ; "TacExtendTac"
    ; "TacThens"
    ; "TacThens3parts"
    ; "TacFirst"
    ; "TacSolve"
    ; "TacTry"
    ; "TacOr"
    ; "TacOnce"
    ; "TacExactlyOnce"
    ; "TacIfThenCatch"
    ; "TacOrelse"
    ; "TacDo"
    ; "TacTimeout"
    ; "TacTime"
    ; "TacRepeat"
    ; "TacProgress"
    ; "TacAbstract"
    ; "TacLetIn"
    ; "TacMatch"
    ; "TacMatchGoal"
    ; "TacFun"
    ; "TacArg"
    ; "TacSelect"
    ; "TacGeneric"
    ; "TacCall"
    ; "TacFreshId"
    ; "Tacexp"
    ; "TacPretype"
    ; "TacNumgoals"
    ]

let rec tactic_tags_in_json acc json =
  let json = unwrap_v json in
  let acc =
    match json with
    | `List (`String tag :: _) when starts_with ~prefix:"Tac" tag ->
      if SSet.mem tag tac_wrappers then acc else SSet.add tag acc
    | _ -> acc
  in
  match json with
  | `Assoc fields ->
    List.fold_left (fun acc (_, value) -> tactic_tags_in_json acc value) acc
      fields
  | `List values -> List.fold_left tactic_tags_in_json acc values
  | _ -> acc

type notation_occurrence =
  { key : string
  ; scope : string option
  ; range : JLang.Range.t option
  }

let notation_key_of_json json =
  let json = unwrap_singleton_list (unwrap_v json) in
  match json with
  | `List [ _entry; `String key ] -> Some key
  | `List (`String _entry :: `String key :: _) -> Some key
  | `List (`List (`String _entry :: _) :: `String key :: _) -> Some key
  | `List (_entry :: key :: _) -> (
    match unwrap_v key with
    | `String key -> Some key
    | _ -> None)
  | _ -> None

let string_payload_of_json json =
  match unwrap_v json with
  | `String s -> Some s
  | _ -> None

let rec option_payload_of_json json =
  let json = unwrap_singleton_list (unwrap_v json) in
  match json with
  | `Null
  | `List [] -> None
  | `List [ x ] -> option_payload_of_json x
  | x -> Some x

let notation_scope_of_json json =
  match option_payload_of_json json with
  | None -> None
  | Some json ->
    let json = unwrap_singleton_list (unwrap_v json) in
    match json with
    | `List (`String "NotationInScope" :: scope_json :: _) ->
      string_payload_of_json scope_json
    | `String "LastLonelyNotation"
    | `List (`String "LastLonelyNotation" :: _) -> None
    | _ -> None

let rec notation_occurrences ~lines acc json =
  let range =
    Stdlib.Option.bind (value_for_key "loc" json) (loc_range_of_json ~lines)
  in
  let json = unwrap_v json in
  let acc =
    match json with
    | `List (`String "CNotation" :: scope_json :: notation_json :: _)
    | `List (`String "CPatNotation" :: scope_json :: notation_json :: _) -> (
      match notation_key_of_json notation_json with
      | Some key ->
        let scope = notation_scope_of_json scope_json in
        { key; scope; range } :: acc
      | None -> acc)
    | `List (`String "VernacNotation" :: _infix :: decl :: _) -> (
      match
        Stdlib.Option.bind
          (value_for_key "ntn_decl_string" decl)
          string_payload_of_json
      with
      | Some key -> { key; scope = None; range } :: acc
      | None -> acc)
    | _ -> acc
  in
  match json with
  | `Assoc fields ->
    List.fold_left
      (fun acc (_, value) -> notation_occurrences ~lines acc value)
      acc fields
  | `List values -> List.fold_left (notation_occurrences ~lines) acc values
  | _ -> acc

let add_hyp_names acc (h : _ Coq.Goals.Reified_goal.hyp) =
  List.fold_left (fun acc name -> SSet.add name acc) acc h.names

let add_goal_hyp_names acc (g : _ Coq.Goals.Reified_goal.t) =
  List.fold_left add_hyp_names acc g.hyps

let local_hyp_names_of_state st =
  match Info.Goals.get_goals ~compact:false ~st with
  | None -> SSet.empty
  | Some goals ->
    let acc = List.fold_left add_goal_hyp_names SSet.empty goals.goals in
    let acc =
      List.fold_left
        (fun acc (l, r) ->
          let acc = List.fold_left add_goal_hyp_names acc l in
          List.fold_left add_goal_hyp_names acc r)
        acc goals.stack
    in
    let acc = List.fold_left add_goal_hyp_names acc goals.shelf in
    List.fold_left add_goal_hyp_names acc goals.given_up

let goal_hyp_of_reified (h : string Coq.Goals.Reified_goal.hyp) : GoalHyp.t =
  GoalHyp.{ names = h.names; def = h.def; ty = h.ty }

let goal_of_reified (g : string Coq.Goals.Reified_goal.t) : Goal.t =
  Goal.
    { evar = Evar.repr g.info.evar
    ; name = Option.map Names.Id.to_string g.info.name
    ; hyps = List.map goal_hyp_of_reified g.hyps
    ; ty = g.ty
    }

let goal_state_of_reified (g : (string, Coq.Pp_t.t) Coq.Goals.reified) :
    GoalState.t =
  GoalState.
    { goals = List.map goal_of_reified g.goals
    ; stack =
        List.map
          (fun (l, r) -> (List.map goal_of_reified l, List.map goal_of_reified r))
          g.stack
    ; bullet = Option.map Coq.Pp_t.to_string g.bullet
    ; shelf = List.map goal_of_reified g.shelf
    ; given_up = List.map goal_of_reified g.given_up
    }

let pp_term_string ~token env sigma t =
  Info.Goals.to_pp ~token env sigma t |> Coq.Pp_t.to_string

let goals_of_state ~token ~(st : Coq.State.t) =
  Info.Goals.goals ~token ~pr:pp_term_string ~compact:false ~st
  |> result_of_execution
  |> function
  | Some (Some goals) -> Some (goal_state_of_reified goals)
  | _ -> None

let dep_of_global (gr : Names.GlobRef.t) =
  try
    let name =
      Nametab.shortest_qualid_of_global Names.Id.Set.empty gr
      |> Libnames.string_of_qualid
    in
    let logical_path =
      let full_path = Nametab.path_of_global gr in
      let dirpath, _ = Libnames.repr_path full_path in
      Names.DirPath.to_string dirpath
    in
    let rec library_path_of_dirpath dirpath =
      match Loadpath.locate_absolute_library dirpath with
      | Ok path -> Some (CUnix.string_of_physical_path path)
      | Error _ -> (
        match Names.DirPath.repr dirpath with
        | _ :: (_ :: _ as parent_rev) ->
          library_path_of_dirpath (Names.DirPath.make parent_rev)
        | _ -> None)
    in
    let physical_path =
      let full_path = Nametab.path_of_global gr in
      let dirpath, _ = Libnames.repr_path full_path in
      library_path_of_dirpath dirpath
    in
    Some Dep.{ name; logical_path; physical_path; locations = [] }
  with _ -> None

let compare_dep (d1 : Dep.t) (d2 : Dep.t) =
  match String.compare d1.logical_path d2.logical_path with
  | 0 -> String.compare d1.name d2.name
  | c -> c

let dep_of_axiom = function
  | Printer.Constant kn -> dep_of_global (Names.GlobRef.ConstRef kn)
  | Printer.Guarded gr
  | Printer.TypeInType gr -> dep_of_global gr
  | Printer.Positive mind
  | Printer.UIP mind -> dep_of_global (Names.GlobRef.IndRef (mind, 0))

let axioms_of_proof ~token ~(st : Coq.State.t) ~(proof_name : string) =
  let collect () =
    try
      let qid = Libnames.qualid_of_string proof_name in
      let gr = Nametab.locate qid in
      let env = Global.env () in
      let cstr, _ = UnivGen.fresh_global_instance env gr in
      let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
      let opaque_access = (Library.indirect_accessor [@warning "-3"]) in
      let assumptions =
        Assumptions.assumptions opaque_access ts gr cstr
      in
      Printer.ContextObjectMap.fold
        (fun obj _ty acc ->
          match obj with
          | Printer.Axiom (axiom, _parents) -> (
            match dep_of_axiom axiom with
            | Some dep -> dep :: acc
            | None -> acc)
          | _ -> acc)
        assumptions []
      |> List.sort_uniq compare_dep
    with _ -> []
  in
  Coq.State.in_state ~token ~st ~f:(fun () -> collect ()) ()
  |> result_of_execution
  |> Stdlib.Option.value ~default:[]

let resolve_dependency qid =
  try
    let qid = Libnames.qualid_of_string qid in
    let gr = Nametab.locate qid in
    match gr with
    | Names.GlobRef.VarRef _ -> None
    | _ -> dep_of_global gr
  with _ -> None

let range_key (range : JLang.Range.t) =
  let s = range.Lang.Range.start in
  let e = range.end_ in
  Printf.sprintf "%d:%d:%d-%d:%d:%d" s.line s.character s.offset e.line
    e.character e.offset

let notation_occurrence_id ({ key; scope; _ } : notation_occurrence) =
  match scope with
  | None -> key
  | Some scope -> key ^ "\x1f" ^ scope

let notation_occurrence_of_id id =
  match String.index_opt id '\x1f' with
  | None -> (id, None)
  | Some i ->
    let key = String.sub id 0 i in
    let scope = String.sub id (i + 1) (String.length id - i - 1) in
    (key, Some scope)

let notation_ref_key (ntn : NotationRef.t) =
  Printf.sprintf "%s\x1f%s" ntn.name ntn.logical_path

let unresolved_notation_ref key =
  NotationRef.{ name = key; logical_path = ""; locations = [] }

let resolve_notation_ref ~key ~scope =
  let delimiters =
    match scope with
    | None -> None
    | Some scope -> (
      try
        let scope = Notation.find_scope scope in
        Notation.scope_delimiters scope
      with _ -> None)
  in
  try
    let gr =
      Notation.interp_notation_as_global_reference ~head:false
        (fun _ -> true) key delimiters
    in
    match dep_of_global gr with
    | None -> None
    | Some dep ->
      Some
        NotationRef.
          { name = key
          ; logical_path = dep.logical_path
          ; locations = []
          }
  with _ -> None

let deps_from_ast_json ~token ~(st : Coq.State.t) ~(locals : SSet.t)
    ~lines ast_json =
  let occurrences =
    match ast_json with
    | None -> []
    | Some ast_json ->
      qualid_occurrences ~lines [] ast_json
      |> List.filter (fun { qid; _ } ->
             let base = basename_of_qualid qid in
             String.contains qid '.' || not (SSet.mem base locals))
  in
  let qids =
    List.fold_left (fun acc { qid; _ } -> SSet.add qid acc) SSet.empty occurrences
  in
  if SSet.is_empty qids then []
  else
    let resolve_all qids =
      SSet.fold
        (fun qid acc ->
          match resolve_dependency qid with
          | Some dep -> SMap.add qid dep acc
          | None -> acc)
        qids SMap.empty
    in
    Coq.State.in_state ~token ~st ~f:resolve_all qids
    |> result_of_execution
    |> Stdlib.Option.fold ~none:[] ~some:(fun by_qid ->
           let by_name =
             List.fold_left
               (fun by_name ({ qid; range } : qualid_occurrence) ->
                 match SMap.find_opt qid by_qid with
                 | None -> by_name
                 | Some dep ->
                   let existing =
                     match SMap.find_opt dep.Dep.name by_name with
                     | None -> (dep, SMap.empty)
                     | Some pair -> pair
                   in
                   let dep0, loc_map = existing in
                   let loc_map =
                     match range with
                     | None -> loc_map
                     | Some range ->
                       let key = range_key range in
                       SMap.add key Dep.Location.{ range } loc_map
                   in
                   SMap.add dep.Dep.name (dep0, loc_map) by_name)
               SMap.empty occurrences
           in
           SMap.bindings by_name
           |> List.map (fun (_name, (dep, loc_map)) ->
                  Dep.{ dep with locations = List.map snd (SMap.bindings loc_map) }))

let tactic_tags_from_ast_json ast_json =
  match ast_json with
  | None -> []
  | Some ast_json -> tactic_tags_in_json SSet.empty ast_json |> SSet.elements

let notations_from_ast_json ~token ~(st : Coq.State.t) ~lines ast_json =
  match ast_json with
  | None -> []
  | Some ast_json ->
    let occurrences = notation_occurrences ~lines [] ast_json in
    let ids =
      List.fold_left
        (fun acc occ -> SSet.add (notation_occurrence_id occ) acc)
        SSet.empty occurrences
    in
    if SSet.is_empty ids then []
    else
      let resolve_all ids =
        SSet.fold
          (fun id acc ->
            let key, scope = notation_occurrence_of_id id in
            let ntn =
              match resolve_notation_ref ~key ~scope with
              | Some ntn -> ntn
              | None -> unresolved_notation_ref key
            in
            SMap.add id ntn acc)
          ids SMap.empty
      in
      Coq.State.in_state ~token ~st ~f:resolve_all ids
      |> result_of_execution
      |> Stdlib.Option.fold ~none:[] ~some:(fun by_id ->
             let by_notation =
               List.fold_left
                 (fun by_notation ({ key; range; _ } as occ) ->
                   let id = notation_occurrence_id occ in
                   let ntn =
                     match SMap.find_opt id by_id with
                     | Some ntn -> ntn
                     | None -> unresolved_notation_ref key
                   in
                   let key = notation_ref_key ntn in
                   let existing =
                     match SMap.find_opt key by_notation with
                     | None -> (ntn, SMap.empty)
                     | Some pair -> pair
                   in
                   let ntn0, loc_map = existing in
                   let loc_map =
                     match range with
                     | None -> loc_map
                     | Some range ->
                       let key = range_key range in
                       SMap.add key Dep.Location.{ range } loc_map
                   in
                   SMap.add key (ntn0, loc_map) by_notation)
                 SMap.empty occurrences
             in
             SMap.bindings by_notation
             |> List.map (fun (_name, (ntn, loc_map)) ->
                    NotationRef.
                      { ntn with locations = List.map snd (SMap.bindings loc_map) }))

type proof_acc =
  { proof_id : int
  ; name : string
  ; start_range : JLang.Range.t
  ; mutable statement_raw : string option
  ; mutable statement_notations : NotationRef.t list
  ; mutable axioms : Dep.t list option
  ; mutable initial_goals : GoalState.t option
  ; mutable initial_goals_set : bool
  ; mutable next_step : int
  ; mutable steps_rev : Step.t list
  }

let add_step (acc : proof_acc) ~range ~raw ~tactic_tags ~notations ~deps ~goals_after =
  let step =
    Step.{ index = acc.next_step; range; raw; tactic_tags; notations; deps; goals_after }
  in
  acc.next_step <- acc.next_step + 1;
  acc.steps_rev <- step :: acc.steps_rev

let mk_dump ~token ~(doc : Doc.t) =
  let asts =
    Doc.asts doc |> List.map (fun ast -> CoqJ.Ast.to_yojson ast.Doc.Node.Ast.v)
  in
  let proofs = Hashtbl.create 17 in
  let order_rev : proof_acc list ref = ref [] in
  let next_id = ref 1 in
  let ensure_proof name range =
    match Hashtbl.find_opt proofs name with
    | Some p -> p
    | None ->
      let p =
        { proof_id = !next_id
        ; name
        ; start_range = range
        ; statement_raw = None
        ; statement_notations = []
        ; axioms = None
        ; initial_goals = None
        ; initial_goals_set = false
        ; next_step = 1
        ; steps_rev = []
        }
      in
      incr next_id;
      Hashtbl.add proofs name p;
      order_rev := p :: !order_rev;
      p
  in
  let contents = doc.contents in
  List.iter
    (fun (node : Doc.Node.t) ->
      let pre_st = state_before ~doc node in
      let pre_name = proof_name_of_state pre_st in
      let post_name = proof_name_of_state node.state in
      let proof_name = match post_name with Some n -> Some n | None -> pre_name in
      match proof_name with
      | None -> ()
      | Some proof_name ->
        let p = ensure_proof proof_name node.range in
        let raw = Fleche.Contents.extract_raw ~contents ~range:node.range in
        let ast_json = Option.map (fun n -> CoqJ.Ast.to_yojson n.Doc.Node.Ast.v) node.ast in
        let tactic_tags = tactic_tags_from_ast_json ast_json in
        let notations = notations_from_ast_json ~token ~st:pre_st ~lines:contents.lines ast_json in
        if p.statement_raw = None then (
          match (pre_name, post_name) with
          | None, Some _ ->
            p.statement_raw <- Some raw;
            p.statement_notations <- notations
          | _ -> ());
        if p.axioms = None then (
          match (pre_name, post_name) with
          | Some _, None ->
            p.axioms <-
              Some (axioms_of_proof ~token ~st:node.state ~proof_name:p.name)
          | _ -> ());
        let goals_after = goals_of_state ~token ~st:node.state in
        if not p.initial_goals_set then (
          let candidate_initial_goals =
            match (pre_name, post_name) with
            | None, Some _ -> goals_after
            | Some _, _ -> goals_of_state ~token ~st:pre_st
            | None, None -> None
          in
          match candidate_initial_goals with
          | Some goals ->
            p.initial_goals <- Some goals;
            p.initial_goals_set <- true
          | None -> ());
        let locals = local_hyp_names_of_state pre_st in
        let deps = deps_from_ast_json ~token ~st:pre_st ~locals ~lines:contents.lines ast_json in
        add_step p ~range:node.range ~raw ~tactic_tags ~notations ~deps ~goals_after)
    doc.nodes;
  let proofs =
    List.rev !order_rev
    |> List.map (fun (p : proof_acc) ->
           let steps = List.rev p.steps_rev in
           let statement, statement_notations =
             match (p.statement_raw, steps) with
             | Some s, _ -> (s, p.statement_notations)
             | None, Step.{ raw; notations; _ } :: _ -> (raw, notations)
             | None, [] -> ("", [])
           in
           Proof.
             { proof_id = p.proof_id
             ; name = p.name
             ; start_range = p.start_range
             ; statement
             ; statement_notations
             ; axioms = Stdlib.Option.value ~default:[] p.axioms
             ; initial_goals = p.initial_goals
             ; steps
             })
  in
  { astdump_jsonl = asts; proofs }

let dump ~io ~token ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[proofdepsdump plugin] dumping for %s ..." uri_str;
  let base = Lang.LUri.File.to_string_file uri in
  let out_file = base ^ ".json.proofdepsdump" in
  let out_file_ast = base ^ ".json.proofdepsdump.ast" in
  let payload = mk_dump ~token ~doc in
  let f fmt json = Yojson.Safe.pretty_print fmt json in
  Coq.Compat.format_to_file ~file:out_file ~f (proofs_to_yojson payload);
  Coq.Compat.format_to_file ~file:out_file_ast ~f (ast_to_yojson payload);
  Io.Report.msg ~io ~lvl "[proofdepsdump plugin] dump for %s completed" uri_str

let main () = Theory.Register.Completed.add dump
let () = main ()
