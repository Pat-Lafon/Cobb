open Mtyped
open Term
module Env = Zzenv

(** calls poirot to get AST of source_file *)
let process meta_config_file source_file () =
  let () = Env.load_meta meta_config_file in
  let code = Commands.Cre.preprocess source_file () in
  code

(** returns "frequency_gen" as ('t, string) typed *)
let replace_bool_gen_string (s : ('t, string) typed) : ('t, string) typed = 
  s #-> (function _ -> "frequency_gen")

let is_bool_gen (s : ('t, string) typed) : bool =
  s.x = "bool_gen"

(** recursively traverses through AST to find and replace bool_gen with frequency_gen *)
let rec replace_bool_gen (t : ('t, 't term) typed) : ('t, 't term) typed = 
  t #-> ( function
  | CErr -> CErr
  | CVal t -> CVal t #-> replace_bool_gen_value
  (* thunkifies branches *)
  | CLetE { 
      lhs; 
      rhs = { x = CApp { appf = { x = VVar {x = "bool_gen"; ty }; ty = ty2} ; apparg }; ty = ty3 }; 
      body = { x = CMatch { matched ; match_cases = [
        CMatchcase
          { 
            constructor = { x = "True"; ty = ty_t }; 
            args = []; 
            exp = exp1;
          };
        CMatchcase
          {
            constructor = { x = "False"; ty = ty_f };
            args = [];
            exp = exp2;
          };
      ]; }; ty = ty4} } ->
        CLetE {     (* w0 = get_weight_idx *)
          lhs = ("w0" #: ty);
          rhs = { x = CApp {
            appf = { x = VVar ("get_weight_idx" #: ty); ty = Nt.Ty_any};
            apparg = {x = VConst (I 0); ty = Nt.Ty_any};
          }; ty = Nt.Ty_any}; 
          body = { x = CLetE {    (* w1 = get_weight_idx *)
            lhs = ("w1" #: ty);
            rhs = { x = CApp {
              appf = { x = VVar ("get_weight_idx" #: ty); ty = Nt.Ty_any};
              apparg = {x = VConst (I 1); ty = Nt.Ty_any};
            }; ty = Nt.Ty_any}; 
            body = { x = CLetE {    (* let (base_case) = frequency_gen_list_new (w0, []) *)
              lhs = ("base_case" #: ty);
              rhs = { x = CApp { 
                appf = { x = VVar (replace_bool_gen_string "bool_gen"#:ty); ty = ty2}; 
                apparg = { x = VTu [
                  { x = VVar ("w0" #: Nt.Ty_any); ty = Nt.Ty_any};
                  { x = VLam {
                      lamarg = ("_" #: ty); 
                      body = exp1;
                  }; ty = Nt.Ty_any}; ]    
                  ; ty = Nt.Ty_any (* placeholder *) }
                }; ty = ty3 }; 
              body = { x = CLetE {    (* let (recursive_case) = base_case (w0, ...) *)
                lhs = ("recursive_case" #: ty);
                rhs = { x = CApp {
                  appf = { x = VVar ("base_case" #: ty); ty = Nt.Ty_any};
                  apparg = { x = VTu [
                    { x = VVar ("w1" #: Nt.Ty_any); ty = Nt.Ty_any};
                    { x = VLam {
                        lamarg = ("_" #: ty); 
                        body = exp2;
                    }; ty = Nt.Ty_any}; ]    
                    ; ty = Nt.Ty_any (* placeholder *) }
                }; ty = Nt.Ty_any};
                body = { x = CVal { x = VVar ("recursive_case" #: ty); ty = Nt.Ty_any} ; ty = Nt.Ty_any}
              }; ty = Nt.Ty_any (* placeholder *) };
            }; ty = Nt.Ty_any}
          }; ty = Nt.Ty_any}}
  | CLetE { lhs; rhs; body} -> 
    CLetE {
      lhs;
      rhs = replace_bool_gen rhs;
      body = replace_bool_gen body
    }
  | CLetDeTu { turhs; tulhs; body} ->
    CLetDeTu {
      turhs = turhs #-> replace_bool_gen_value;
      tulhs; 
      body = replace_bool_gen body;
    }
  | CApp { appf; apparg} ->
    CApp {
      appf = appf #-> replace_bool_gen_value;
      apparg = apparg #-> replace_bool_gen_value;
  }
  | CAppOp {op; appopargs} -> 
    CAppOp {
      op;
      appopargs = (List.map (function y -> y #-> replace_bool_gen_value ) appopargs)
    }
  | CMatch
  (* To rewrite matches on True/False to true/false, from Cobb_postprocess*)
  {
    matched;
    match_cases =
      [
        CMatchcase
          { 
            constructor = { x = "True"; ty = ty_t }; 
            args = []; 
            exp = exp1 
          };
        CMatchcase
          {
            constructor = { x = "False"; ty = ty_f };
            args = [];
            exp = exp2;
          };
      ];
  } -> 
    CMatch
        {
          matched;
          match_cases =
            [
              CMatchcase
                {
                  constructor = "true"#:ty_t;
                  args = [];
                  exp = replace_bool_gen exp1;
                };
              CMatchcase
                {
                  constructor = "false"#:ty_f;
                  args = [];
                  exp = replace_bool_gen exp2;
                };
            ];
        }
  | CMatch { matched; match_cases } ->
    CMatch {
      matched = matched #-> replace_bool_gen_value;
      match_cases =
        List.map (function (CMatchcase {constructor; args; exp}) -> 
          CMatchcase {
            constructor;
            args;
            exp = replace_bool_gen exp;
          }
        )
        match_cases
    }
  )
and replace_bool_gen_value (v : 't value) =
  match v with 
  | VConst _ -> v
  (* bool_gen is a VVar *)
  | VVar s -> 
    if s.x = "bool_gen" then
      VVar (replace_bool_gen_string s)
    else
      VVar s
  | VLam {lamarg; body} -> 
    VLam  {
      lamarg;
      body = replace_bool_gen body;
    }
  | VFix { fixname; fixarg; body } -> 
    VFix {
      fixname;
      fixarg;
      body = replace_bool_gen body;
    }
  | VTu l -> 
    (* tuples *)
    VTu (List.map (function y -> y #-> replace_bool_gen_value ) l)

(* #-> applies function to arg, returning it as `typed` *)

(** gets the body of the function *)
let get_function = function
| Language.MFuncImp {name; if_rec;body; _} -> Some (name, if_rec, body) 
| _ -> None


let get_value_constructor (v : 't value) =
  match v with 
  | VConst _-> "const"
  | VVar _ -> "var"
  | VLam _ -> "lam"
  | VFix _ -> "fix"
  | VTu _ -> "tu"

(* finds what type of term bool_gen is (CVal) *)
(* matches for term *)
let peek (t : ('t, 't term) typed) =
  match t.x with 
  | CVal {x = value;_} -> get_value_constructor value
  | _ -> failwith "not CVal"

let print_code (config:string) (source:string) =

  (* calls poirot preprocess to get AST of source file *)
  let code = process config source () in

  (* gets the first item, (gets the function and ignores the type annotation) *)
  let first_item = (Array.get (Array.of_list code) 0) in

  (* converts the body into terms *)
  let (name, if_rec, body) = 
    match get_function first_item with
    | Some (name, if_rec, body) -> (name, if_rec, body)
    | None -> failwith "Expected a function but got None"
  in

  (* gets string of AST *)
  let body_str = Language.FrontendTyped.layout_typed_term body in

  
  print_endline name.x;
  print_endline body_str;
  let () = print_endline (peek body) 
in ()

(** returns string version of AST *)
let final_program_to_string name if_rec new_body : string = 
  let body_as_item = 
    Item.MFuncImp
      {
        name = name;
        if_rec = if_rec;
        body = new_body;
      }
  in
  (* Change to (fun x -> None) to remove type annotations and improve clarity *)
  let reconstructed_body = Item.map_item (fun x -> None) body_as_item in
  Frontend_opt.To_item.layout_item reconstructed_body


let transform_program (config : string) (source : string ) = 
  (* temporarily removes open because poirot can't read it *)
  let ic = open_in source in
  let lines = ref [] in

  try
    while true do
      let line = input_line ic in
      lines := line :: !lines
    done
  with 
    End_of_file -> close_in ic;
  
  let lines = List.rev !lines in

  let oc = open_out source in
  List.iter (fun line -> 
    match line with
    | _ when String.length line >= 4 && String.sub line 0 4 <> "open" ->
      output_string oc (line ^ "\n");
    | _ -> ()
  ) lines;
  close_out oc;
  
  let code = process config source () in

  (* adds open back *)

  let oc = open_out source in
  (* output_string oc "open Combinators\n";
  output_string oc "open Frequency_combinators\n"; *)
  List.iter (fun line -> output_string oc (line ^ "\n")) lines;
  close_out oc;

  let code_arr = Array.of_list code in
  (* (gets the function and ignores the type annotation) *)
  print_int (Array.length code_arr);
  for x = 0 to (Array.length code_arr) - 1 do
    match get_function code_arr.(x) with
    | Some (name, if_rec, body) -> 
      (* replaces bool_gen with frequency_gen*)
      let new_body = replace_bool_gen body in
      let new_code = final_program_to_string name if_rec new_body in
      
      (* prints new body *)
      let () = print_endline new_code in

      (* prints program to file *)
      let filename = String.sub source 0 ( (String.length source) - 3) ^ "_freq.ml" in
      let oc = open_out filename in
      output_string oc "open Combinators\n";
      output_string oc "open Frequency_combinators\n";
      output_string oc new_code;
      close_out oc
    | None -> ()
  done


let () =
  try 
    let config_file = "./underapproximation_type/meta-config.json" in
    let source_file = Array.get Sys.argv 1 in

    transform_program config_file source_file 
  with
   | Invalid_argument s -> print_endline "Usage: dune exec frequify program_file"