open Mtyped
open Term
open Pieces

let rec remove_excess_ast_aux (t : ('t, 't term) typed) =
  match t.x with
  | CVal { x = VVar { x = "true"; _ }; ty } ->
      (CVal { x = VConst (B true); ty })#:t.ty
  | CVal { x = VVar { x = "false"; _ }; ty } ->
      (CVal { x = VConst (B false); ty })#:t.ty
  | CAppOp { op = { x = DtConstructor "Nil"; ty }; appopargs } ->
      (CAppOp { op = { x = DtConstructor "[]"; ty }; appopargs })#:t.ty
  | CAppOp { op = { x = DtConstructor "Cons"; ty }; appopargs } ->
      (CAppOp { op = { x = DtConstructor "::"; ty }; appopargs })#:t.ty
  | CErr | CApp _ | CAppOp _ | CVal _ -> t
  | CLetE
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        {
                          constructor = { x = "True" | "false"; _ };
                          args = [];
                          exp;
                        };
                      CMatchcase
                        {
                          constructor = { x = "False" | "false"; _ };
                          args = [];
                          exp = { x = CVal { x = VVar f; _ }; _ };
                        };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x && is_prefix f.x ~prefix:"Hole") ->
      (* let _ = layout_typed_term t |> print_endline in
         let _ = f.x |> print_endline in *)
      remove_excess_ast_aux exp
  | CLetE
      (* True branch Err *)
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        {
                          constructor = { x = "True" | "true"; _ };
                          args = [];
                          exp = { x = CErr; _ };
                        };
                      CMatchcase
                        {
                          constructor = { x = "False" | "false"; _ };
                          args = [];
                          exp;
                        };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x) ->
      remove_excess_ast_aux exp
  | CLetE
      (* False branch Err *)
      {
        lhs;
        rhs =
          {
            x =
              CApp
                {
                  appf = { x = VVar { x = "bool_gen"; _ }; _ };
                  apparg = { x = VConst U; _ };
                };
            _;
          };
        body =
          {
            x =
              CMatch
                {
                  matched = { x = VVar v; _ };
                  match_cases =
                    [
                      CMatchcase
                        {
                          constructor = { x = "True" | "true"; _ };
                          args = [];
                          exp;
                        };
                      CMatchcase
                        {
                          constructor = { x = "False" | "false"; _ };
                          args = [];
                          exp = { x = CErr; _ };
                        };
                    ];
                };
            _;
          };
      }
    when Core.String.(lhs.x = v.x) ->
      remove_excess_ast_aux exp
  | CLetE { lhs; rhs = { x = CVal { x = VVar v; _ }; _ }; body } when lhs = v ->
      remove_excess_ast_aux body
  | CLetE { lhs; rhs; body } ->
      (CLetE { lhs; rhs; body = remove_excess_ast_aux body })#:t.ty
  | CLetDeTu { turhs; tulhs; body } ->
      (CLetDeTu { turhs; tulhs; body = remove_excess_ast_aux body })#:t.ty
  | CMatch
      (* To rewrite matches on True/False to true/false*)
      {
        matched;
        match_cases =
          [
            CMatchcase
              { constructor = { x = "True"; ty = ty_t }; args = []; exp = exp1 };
            CMatchcase
              {
                constructor = { x = "False"; ty = ty_f };
                args = [];
                exp = exp2;
              };
          ];
      } ->
      remove_excess_ast_aux
        (CMatch
           {
             matched;
             match_cases =
               [
                 CMatchcase
                   {
                     constructor = "true"#:ty_t;
                     args = [];
                     exp = remove_excess_ast_aux exp1;
                   };
                 CMatchcase
                   {
                     constructor = "false"#:ty_f;
                     args = [];
                     exp = remove_excess_ast_aux exp2;
                   };
               ];
           })#:t.ty
  | CMatch { matched; match_cases } ->
      (CMatch
         {
           matched;
           match_cases =
             List.map
               (fun (CMatchcase { constructor; args; exp }) ->
                 CMatchcase
                   { constructor; args; exp = remove_excess_ast_aux exp })
               match_cases;
         })#:t.ty

let rec nd_join_list (t : (_, _ term) typed list) : (_, _ term) typed =
  match t with
  | [] -> failwith "Empty list"
  | [ x ] -> x
  | x :: xs -> Pieces.mk_ND_choice x (nd_join_list xs)

(** Take the body of the function, a lambda to convert the body into full code,
    and output it somewhere after some cleanup. *)
let final_program_to_string (reconstruct_code_with_new_body : _ -> _ Item.item)
    new_body : string =
  let new_frontend_prog =
    new_body |> reconstruct_code_with_new_body |> Item.map_item (fun x -> None)
  in

  Frontend_opt.To_item.layout_item new_frontend_prog

let remove_underscores_in_variable_names_string (x : string) : string =
  match String.split_on_char '_' x with
  | [] -> failwith "Empty string"
  | [ x ] -> x
  | [ x; y ] when int_of_string_opt y |> Option.is_some ->
      String.concat "ccc" [ x; y ]
  | _ -> x

let remove_helper (x : ('t, string) typed) : ('t, string) typed =
  x#->remove_underscores_in_variable_names_string

let rec remove_underscores_in_variable_names_value (x : 't value) : 't value =
  match x with
  | VConst _ -> x
  | VVar t -> VVar (remove_helper t)
  | VLam { lamarg; body } ->
      VLam
        {
          lamarg = remove_helper lamarg;
          body = remove_underscores_in_variable_names_typed body;
        }
  | VFix { fixname; fixarg; body } ->
      assert (String.split_on_char '_' fixname.x |> List.length = 1);
      VFix
        {
          fixname;
          fixarg = remove_helper fixarg;
          body = remove_underscores_in_variable_names_typed body;
        }
  | VTu l ->
      VTu (List.map (fun y -> y#->remove_underscores_in_variable_names_value) l)

(** TODO: This is a hack until I come up with a better uniqufiy/renaming
    strategy for Poirot that doesn't clobber over existing names*)
and remove_underscores_in_variable_names_typed (x : ('t, 't term) typed) :
    ('t, 't term) typed =
  x #-> ( function
  | CErr -> CErr
  | CVal t -> CVal t#->remove_underscores_in_variable_names_value
  | CLetE { lhs; rhs; body } ->
      CLetE
        {
          lhs = remove_helper lhs;
          rhs = remove_underscores_in_variable_names_typed rhs;
          body = remove_underscores_in_variable_names_typed body;
        }
  | CLetDeTu { turhs; tulhs; body } ->
      CLetDeTu
        {
          turhs = turhs#->remove_underscores_in_variable_names_value;
          tulhs = List.map remove_helper tulhs;
          body = remove_underscores_in_variable_names_typed body;
        }
  | CApp { appf; apparg } ->
      CApp
        {
          appf = appf#->remove_underscores_in_variable_names_value;
          apparg = apparg#->remove_underscores_in_variable_names_value;
        }
  | CAppOp { op; appopargs } ->
      CAppOp
        {
          op;
          appopargs =
            List.map
              (fun x -> x#->remove_underscores_in_variable_names_value)
              appopargs;
        }
  | CMatch { matched; match_cases } ->
      CMatch
        {
          matched = matched#->remove_underscores_in_variable_names_value;
          match_cases =
            List.map
              (fun (CMatchcase { constructor; args; exp }) ->
                CMatchcase
                  {
                    constructor;
                    args = List.map remove_helper args;
                    exp = remove_underscores_in_variable_names_typed exp;
                  })
              match_cases;
        } )
