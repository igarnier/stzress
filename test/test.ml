open Stzress

module Micheline = struct
  type annot = string list

  type ('l, 'p) node =
    | Int of 'l * Z.t
    | String of 'l * string
    | Bytes of 'l * Bytes.t
    | Prim of 'l * 'p * ('l, 'p) node list * annot
    | Seq of 'l * ('l, 'p) node list

  type canonical_location = int

  type 'p canonical = Canonical of (canonical_location, 'p) node

  let canonical_location_encoding =
    let open Data_encoding in
    def
      "micheline.location"
      ~title:"Canonical location in a Micheline expression"
      ~description:
        "The location of a node in a Micheline expression tree in prefix \
         order, with zero being the root and adding one for every basic node, \
         sequence and primitive application."
    @@ int31

  let location = function
    | Int (loc, _) -> loc
    | String (loc, _) -> loc
    | Bytes (loc, _) -> loc
    | Seq (loc, _) -> loc
    | Prim (loc, _, _, _) -> loc

  let annotations = function
    | Int (_, _) -> []
    | String (_, _) -> []
    | Bytes (_, _) -> []
    | Seq (_, _) -> []
    | Prim (_, _, _, annots) -> annots

  let root (Canonical expr) = expr

  (* We use a defunctionalized CPS implementation. The type below corresponds to that of
     continuations. *)
  type ('l, 'p, 'la, 'pa) cont =
    | Seq_cont of 'la * ('l, 'p, 'la, 'pa) list_cont
    | Prim_cont of 'la * 'pa * annot * ('l, 'p, 'la, 'pa) list_cont

  and ('l, 'p, 'la, 'pa) list_cont =
    | List_cont of
        ('l, 'p) node list * ('la, 'pa) node list * ('l, 'p, 'la, 'pa) cont
    | Return

  let strip_locations (type a b) (root : (a, b) node) : b canonical =
    let id =
      let id = ref (-1) in
      fun () ->
        incr id ;
        !id
    in
    let rec strip_locations l k =
      let id = id () in
      match l with
      | Int (_, v) -> (apply [@tailcall]) k (Int (id, v))
      | String (_, v) -> (apply [@tailcall]) k (String (id, v))
      | Bytes (_, v) -> (apply [@tailcall]) k (Bytes (id, v))
      | Seq (_, seq) ->
          (strip_locations_list [@tailcall]) seq [] (Seq_cont (id, k))
      | Prim (_, name, seq, annots) ->
          (strip_locations_list [@tailcall])
            seq
            []
            (Prim_cont (id, name, annots, k))
    and strip_locations_list ls acc k =
      match ls with
      | [] -> (apply_list [@tailcall]) k (List.rev acc)
      | x :: tl -> (strip_locations [@tailcall]) x (List_cont (tl, acc, k))
    and apply k node =
      match k with
      | List_cont (tl, acc, k) ->
          (strip_locations_list [@tailcall]) tl (node :: acc) k
      | Return -> node
    and apply_list k node_list =
      match k with
      | Seq_cont (id, k) -> (apply [@tailcall]) k (Seq (id, node_list))
      | Prim_cont (id, name, annots, k) ->
          (apply [@tailcall]) k (Prim (id, name, node_list, annots))
    in
    Canonical (strip_locations root Return)

  let map_node :
      type la lb pa pb.
      (la -> lb) -> (pa -> pb) -> (la, pa) node -> (lb, pb) node =
   fun fl fp node ->
    let rec map_node fl fp node k =
      match node with
      | Int (loc, v) -> (apply [@tailcall]) fl fp k (Int (fl loc, v))
      | String (loc, v) -> (apply [@tailcall]) fl fp k (String (fl loc, v))
      | Bytes (loc, v) -> (apply [@tailcall]) fl fp k (Bytes (fl loc, v))
      | Seq (loc, seq) ->
          (map_node_list [@tailcall]) fl fp seq [] (Seq_cont (fl loc, k))
      | Prim (loc, name, seq, annots) ->
          (map_node_list [@tailcall])
            fl
            fp
            seq
            []
            (Prim_cont (fl loc, fp name, annots, k))
    and map_node_list fl fp ls acc k =
      match ls with
      | [] -> (apply_list [@tailcall]) fl fp k (List.rev acc)
      | x :: tl -> (map_node [@tailcall]) fl fp x (List_cont (tl, acc, k))
    and apply fl fp k node =
      match k with
      | List_cont (tl, acc, k) ->
          (map_node_list [@tailcall]) fl fp tl (node :: acc) k
      | Return -> node
    and apply_list fl fp k node_list =
      match k with
      | Seq_cont (id, k) -> (apply [@tailcall]) fl fp k (Seq (id, node_list))
      | Prim_cont (id, name, annots, k) ->
          (apply [@tailcall]) fl fp k (Prim (id, name, node_list, annots))
    in
    (map_node [@tailcall]) fl fp node Return

  type semantics = V0 | V1

  let internal_canonical_encoding ~semantics ~variant prim_encoding =
    let open Data_encoding in
    let int_encoding = obj1 (req "int" z) in
    let string_encoding = obj1 (req "string" string) in
    let bytes_encoding = obj1 (req "bytes" bytes) in
    let int_encoding tag =
      case
        tag
        int_encoding
        ~title:"Int"
        (function Int (_, v) -> Some v | _ -> None)
        (fun v -> Int (0, v))
    in
    let string_encoding tag =
      case
        tag
        string_encoding
        ~title:"String"
        (function String (_, v) -> Some v | _ -> None)
        (fun v -> String (0, v))
    in
    let bytes_encoding tag =
      case
        tag
        bytes_encoding
        ~title:"Bytes"
        (function Bytes (_, v) -> Some v | _ -> None)
        (fun v -> Bytes (0, v))
    in
    let seq_encoding tag expr_encoding =
      case
        tag
        (list expr_encoding)
        ~title:"Sequence"
        (function Seq (_, v) -> Some v | _ -> None)
        (fun args -> Seq (0, args))
    in
    let annots_encoding =
      let split s =
        if s = "" && semantics <> V0 then []
        else
          let annots = String.split_on_char ' ' s in
          List.iter
            (fun a ->
              if String.length a > 255 then failwith "Oversized annotation")
            annots ;
          if String.concat " " annots <> s then
            failwith
              "Invalid annotation string, must be a sequence of valid \
               annotations with spaces" ;
          annots
      in
      splitted
        ~json:(list (Bounded.string 255))
        ~binary:(conv (String.concat " ") split string)
    in
    let application_encoding tag expr_encoding =
      case
        tag
        ~title:"Generic prim (any number of args with or without annot)"
        (obj3
           (req "prim" prim_encoding)
           (dft "args" (list expr_encoding) [])
           (dft "annots" annots_encoding []))
        (function
          | Prim (_, prim, args, annots) -> Some (prim, args, annots)
          | _ -> None)
        (fun (prim, args, annots) -> Prim (0, prim, args, annots))
    in
    let node_encoding =
      mu
        ("micheline." ^ variant ^ ".expression")
        (fun expr_encoding ->
          splitted
            ~json:
              (union
                 ~tag_size:`Uint8
                 [ int_encoding Json_only;
                   string_encoding Json_only;
                   bytes_encoding Json_only;
                   seq_encoding Json_only expr_encoding;
                   application_encoding Json_only expr_encoding ])
            ~binary:
              (union
                 ~tag_size:`Uint8
                 [ int_encoding (Tag 0);
                   string_encoding (Tag 1);
                   seq_encoding (Tag 2) expr_encoding;
                   (* No args, no annot *)
                   case
                     (Tag 3)
                     ~title:"Prim (no args, annot)"
                     (obj1 (req "prim" prim_encoding))
                     (function Prim (_, v, [], []) -> Some v | _ -> None)
                     (fun v -> Prim (0, v, [], []));
                   (* No args, with annots *)
                   case
                     (Tag 4)
                     ~title:"Prim (no args + annot)"
                     (obj2
                        (req "prim" prim_encoding)
                        (req "annots" annots_encoding))
                     (function
                       | Prim (_, v, [], annots) -> Some (v, annots) | _ -> None)
                     (function (prim, annots) -> Prim (0, prim, [], annots));
                   (* Single arg, no annot *)
                   case
                     (Tag 5)
                     ~title:"Prim (1 arg, no annot)"
                     (obj2 (req "prim" prim_encoding) (req "arg" expr_encoding))
                     (function
                       | Prim (_, v, [arg], []) -> Some (v, arg) | _ -> None)
                     (function (prim, arg) -> Prim (0, prim, [arg], []));
                   (* Single arg, with annot *)
                   case
                     (Tag 6)
                     ~title:"Prim (1 arg + annot)"
                     (obj3
                        (req "prim" prim_encoding)
                        (req "arg" expr_encoding)
                        (req "annots" annots_encoding))
                     (function
                       | Prim (_, prim, [arg], annots) ->
                           Some (prim, arg, annots)
                       | _ -> None)
                     (fun (prim, arg, annots) -> Prim (0, prim, [arg], annots));
                   (* Two args, no annot *)
                   case
                     (Tag 7)
                     ~title:"Prim (2 args, no annot)"
                     (obj3
                        (req "prim" prim_encoding)
                        (req "arg1" expr_encoding)
                        (req "arg2" expr_encoding))
                     (function
                       | Prim (_, prim, [arg1; arg2], []) ->
                           Some (prim, arg1, arg2)
                       | _ -> None)
                     (fun (prim, arg1, arg2) ->
                       Prim (0, prim, [arg1; arg2], []));
                   (* Two args, with annots *)
                   case
                     (Tag 8)
                     ~title:"Prim (2 args + annot)"
                     (obj4
                        (req "prim" prim_encoding)
                        (req "arg1" expr_encoding)
                        (req "arg2" expr_encoding)
                        (req "annots" annots_encoding))
                     (function
                       | Prim (_, prim, [arg1; arg2], annots) ->
                           Some (prim, arg1, arg2, annots)
                       | _ -> None)
                     (fun (prim, arg1, arg2, annots) ->
                       Prim (0, prim, [arg1; arg2], annots));
                   (* General case *)
                   application_encoding (Tag 9) expr_encoding;
                   bytes_encoding (Tag 10) ]))
    in
    conv
      (function Canonical node -> node)
      (fun node -> strip_locations node)
      node_encoding

  let canonical_encoding ~variant prim_encoding =
    internal_canonical_encoding ~semantics:V1 ~variant prim_encoding
end

module Printer = struct
  open Micheline

  type location = { comment : string option }

  type node = (location, string) Micheline.node

  let printable ?(comment = fun _ -> None) map_prim expr =
    let map_loc loc = { comment = comment loc } in
    map_node map_loc map_prim (root expr)

  let print_comment ppf text =
    Format.fprintf ppf "/* @[<h>%a@] */" Format.pp_print_text text

  let print_string ppf text =
    Format.fprintf ppf "\"" ;
    String.iter
      (function
        | '"' -> Format.fprintf ppf "\\\""
        | '\n' -> Format.fprintf ppf "\\n"
        | '\r' -> Format.fprintf ppf "\\r"
        | '\b' -> Format.fprintf ppf "\\b"
        | '\t' -> Format.fprintf ppf "\\t"
        | '\\' -> Format.fprintf ppf "\\\\"
        | c -> Format.fprintf ppf "%c" c)
      text ;
    Format.fprintf ppf "\""

  let print_annotations =
    Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_string

  let preformat root =
    let preformat_loc = function
      | { comment = None } -> (false, 0)
      | { comment = Some text } ->
          (String.contains text '\n', String.length text + 1)
    in
    let preformat_annots = function
      | [] -> 0
      | annots -> String.length (String.concat " " annots) + 2
    in
    let rec preformat_expr = function
      | Int (loc, value) ->
          let (cml, csz) = preformat_loc loc in
          Int ((cml, String.length (Z.to_string value) + csz, loc), value)
      | String (loc, value) ->
          let (cml, csz) = preformat_loc loc in
          String ((cml, String.length value + csz, loc), value)
      | Bytes (loc, value) ->
          let (cml, csz) = preformat_loc loc in
          Bytes ((cml, (Bytes.length value * 2) + 2 + csz, loc), value)
      | Prim (loc, name, items, annots) ->
          let (cml, csz) = preformat_loc loc in
          let asz = preformat_annots annots in
          let items = List.map preformat_expr items in
          let (ml, sz) =
            List.fold_left
              (fun (tml, tsz) e ->
                let (ml, sz, _) = location e in
                (tml || ml, tsz + 1 + sz))
              (cml, String.length name + csz + asz)
              items
          in
          Prim ((ml, sz, loc), name, items, annots)
      | Seq (loc, items) ->
          let (cml, csz) = preformat_loc loc in
          let items = List.map preformat_expr items in
          let (ml, sz) =
            List.fold_left
              (fun (tml, tsz) e ->
                let (ml, sz, _) = location e in
                (tml || ml, tsz + 3 + sz))
              (cml, 4 + csz)
              items
          in
          Seq ((ml, sz, loc), items)
    in
    preformat_expr root

  let rec print_expr_unwrapped ppf = function
    | Prim ((ml, s, { comment }), name, args, annot) ->
        let name =
          match annot with
          | [] -> name
          | annots ->
              Format.asprintf "%s @[<h>%a@]" name print_annotations annots
        in
        if (not ml) && s < 80 then (
          if args = [] then Format.fprintf ppf "%s" name
          else
            Format.fprintf
              ppf
              "@[<h>%s %a@]"
              name
              (Format.pp_print_list ~pp_sep:Format.pp_print_space print_expr)
              args ;
          match comment with
          | None -> ()
          | Some text -> Format.fprintf ppf "@ /* %s */" text)
        else (
          if args = [] then Format.fprintf ppf "%s" name
          else if String.length name <= 4 then
            Format.fprintf
              ppf
              "%s @[<v 0>%a@]"
              name
              (Format.pp_print_list print_expr)
              args
          else
            Format.fprintf
              ppf
              "@[<v 2>%s@,%a@]"
              name
              (Format.pp_print_list print_expr)
              args ;
          match comment with
          | None -> ()
          | Some comment -> Format.fprintf ppf "@ %a" print_comment comment)
    | Int ((_, _, { comment }), value) -> (
        match comment with
        | None -> Format.fprintf ppf "%s" (Z.to_string value)
        | Some comment ->
            Format.fprintf
              ppf
              "%s@ %a"
              (Z.to_string value)
              print_comment
              comment)
    | String ((_, _, { comment }), value) -> (
        match comment with
        | None -> print_string ppf value
        | Some comment ->
            Format.fprintf ppf "%a@ %a" print_string value print_comment comment
        )
    | Bytes ((_, _, { comment }), value) -> (
        match comment with
        | None -> Format.fprintf ppf "0x%a" Hex.pp (Hex.of_bytes value)
        | Some comment ->
            Format.fprintf
              ppf
              "0x%a@ %a"
              Hex.pp
              (Hex.of_bytes value)
              print_comment
              comment)
    | Seq ((_, _, { comment = None }), []) -> Format.fprintf ppf "{}"
    | Seq ((ml, s, { comment }), items) ->
        if (not ml) && s < 80 then Format.fprintf ppf "{ @[<h 0>"
        else Format.fprintf ppf "{ @[<v 0>" ;
        (match (comment, items) with
        | (None, _) -> ()
        | (Some comment, []) -> Format.fprintf ppf "%a" print_comment comment
        | (Some comment, _) -> Format.fprintf ppf "%a@ " print_comment comment) ;
        Format.pp_print_list
          ~pp_sep:(fun ppf () -> Format.fprintf ppf " ;@ ")
          print_expr_unwrapped
          ppf
          items ;
        Format.fprintf ppf "@] }"

  and print_expr ppf = function
    | (Prim (_, _, _ :: _, _) | Prim (_, _, [], _ :: _)) as expr ->
        Format.fprintf ppf "(%a)" print_expr_unwrapped expr
    | expr -> print_expr_unwrapped ppf expr

  let with_unbounded_formatter ppf f x =
    let buf = Buffer.create 10000 in
    let sppf = Format.formatter_of_buffer buf in
    Format.pp_set_margin sppf 199999 ;
    Format.pp_set_max_indent sppf 99999 ;
    Format.pp_set_max_boxes sppf 99999 ;
    f sppf x ;
    Format.fprintf sppf "%!" ;
    let lines = String.split_on_char '\n' (Buffer.contents buf) in
    Format.pp_print_list
      ~pp_sep:Format.pp_force_newline
      Format.pp_print_string
      ppf
      lines

  let print_expr_unwrapped ppf expr =
    with_unbounded_formatter ppf print_expr_unwrapped (preformat expr)

  let print_expr ppf expr =
    with_unbounded_formatter ppf print_expr (preformat expr)
end

module Prim = struct
  type prim =
    | K_parameter
    | K_storage
    | K_code
    | D_False
    | D_Elt
    | D_Left
    | D_None
    | D_Pair
    | D_Right
    | D_Some
    | D_True
    | D_Unit
    | I_PACK
    | I_UNPACK
    | I_BLAKE2B
    | I_SHA256
    | I_SHA512
    | I_ABS
    | I_ADD
    | I_AMOUNT
    | I_AND
    | I_BALANCE
    | I_CAR
    | I_CDR
    | I_CHAIN_ID
    | I_CHECK_SIGNATURE
    | I_COMPARE
    | I_CONCAT
    | I_CONS
    | I_CREATE_ACCOUNT
    | I_CREATE_CONTRACT
    | I_IMPLICIT_ACCOUNT
    | I_DIP
    | I_DROP
    | I_DUP
    | I_EDIV
    | I_EMPTY_BIG_MAP
    | I_EMPTY_MAP
    | I_EMPTY_SET
    | I_EQ
    | I_EXEC
    | I_APPLY
    | I_FAILWITH
    | I_GE
    | I_GET
    | I_GET_AND_UPDATE
    | I_GT
    | I_HASH_KEY
    | I_IF
    | I_IF_CONS
    | I_IF_LEFT
    | I_IF_NONE
    | I_INT
    | I_LAMBDA
    | I_LE
    | I_LEFT
    | I_LEVEL
    | I_LOOP
    | I_LSL
    | I_LSR
    | I_LT
    | I_MAP
    | I_MEM
    | I_MUL
    | I_NEG
    | I_NEQ
    | I_NIL
    | I_NONE
    | I_NOT
    | I_NOW
    | I_OR
    | I_PAIR
    | I_UNPAIR
    | I_PUSH
    | I_RIGHT
    | I_SIZE
    | I_SOME
    | I_SOURCE
    | I_SENDER
    | I_SELF
    | I_SELF_ADDRESS
    | I_SLICE
    | I_STEPS_TO_QUOTA
    | I_SUB
    | I_SWAP
    | I_TRANSFER_TOKENS
    | I_SET_DELEGATE
    | I_UNIT
    | I_UPDATE
    | I_XOR
    | I_ITER
    | I_LOOP_LEFT
    | I_ADDRESS
    | I_CONTRACT
    | I_ISNAT
    | I_CAST
    | I_RENAME
    | I_SAPLING_EMPTY_STATE
    | I_SAPLING_VERIFY_UPDATE
    | I_DIG
    | I_DUG
    | I_NEVER
    | I_VOTING_POWER
    | I_TOTAL_VOTING_POWER
    | I_KECCAK
    | I_SHA3
    | I_PAIRING_CHECK
    | I_TICKET
    | I_READ_TICKET
    | I_SPLIT_TICKET
    | I_JOIN_TICKETS
    | T_bool
    | T_contract
    | T_int
    | T_key
    | T_key_hash
    | T_lambda
    | T_list
    | T_map
    | T_big_map
    | T_nat
    | T_option
    | T_or
    | T_pair
    | T_set
    | T_signature
    | T_string
    | T_bytes
    | T_mutez
    | T_timestamp
    | T_unit
    | T_operation
    | T_address
    | T_sapling_transaction
    | T_sapling_state
    | T_chain_id
    | T_never
    | T_bls12_381_g1
    | T_bls12_381_g2
    | T_bls12_381_fr
    | T_ticket

  (* Auxiliary types for error documentation.
     All the prim constructor prefixes must match their namespace. *)
  type namespace =
    | (* prefix "T" *) Type_namespace
    | (* prefix "D" *) Constant_namespace
    | (* prefix "I" *) Instr_namespace
    | (* prefix "K" *) Keyword_namespace

  let namespace = function
    | K_code | K_parameter | K_storage -> Keyword_namespace
    | D_Elt | D_False | D_Left | D_None | D_Pair | D_Right | D_Some | D_True
    | D_Unit ->
        Constant_namespace
    | I_ABS | I_ADD | I_ADDRESS | I_AMOUNT | I_AND | I_APPLY | I_BALANCE
    | I_BLAKE2B | I_CAR | I_CAST | I_CDR | I_CHAIN_ID | I_CHECK_SIGNATURE
    | I_COMPARE | I_CONCAT | I_CONS | I_CONTRACT | I_CREATE_ACCOUNT
    | I_CREATE_CONTRACT | I_DIG | I_DIP | I_DROP | I_DUG | I_DUP | I_EDIV
    | I_EMPTY_BIG_MAP | I_EMPTY_MAP | I_EMPTY_SET | I_EQ | I_EXEC | I_FAILWITH
    | I_GE | I_GET | I_GET_AND_UPDATE | I_GT | I_HASH_KEY | I_IF | I_IF_CONS
    | I_IF_LEFT | I_IF_NONE | I_IMPLICIT_ACCOUNT | I_INT | I_ISNAT | I_ITER
    | I_JOIN_TICKETS | I_KECCAK | I_LAMBDA | I_LE | I_LEFT | I_LEVEL | I_LOOP
    | I_LOOP_LEFT | I_LSL | I_LSR | I_LT | I_MAP | I_MEM | I_MUL | I_NEG | I_NEQ
    | I_NEVER | I_NIL | I_NONE | I_NOT | I_NOW | I_OR | I_PACK | I_PAIR
    | I_PAIRING_CHECK | I_PUSH | I_READ_TICKET | I_RENAME | I_RIGHT
    | I_SAPLING_EMPTY_STATE | I_SAPLING_VERIFY_UPDATE | I_SELF | I_SELF_ADDRESS
    | I_SENDER | I_SET_DELEGATE | I_SHA256 | I_SHA512 | I_SHA3 | I_SIZE
    | I_SLICE | I_SOME | I_SOURCE | I_SPLIT_TICKET | I_STEPS_TO_QUOTA | I_SUB
    | I_SWAP | I_TICKET | I_TOTAL_VOTING_POWER | I_TRANSFER_TOKENS | I_UNIT
    | I_UNPACK | I_UNPAIR | I_UPDATE | I_VOTING_POWER | I_XOR ->
        Instr_namespace
    | T_address | T_big_map | T_bool | T_bytes | T_chain_id | T_contract | T_int
    | T_key | T_key_hash | T_lambda | T_list | T_map | T_mutez | T_nat | T_never
    | T_operation | T_option | T_or | T_pair | T_sapling_state
    | T_sapling_transaction | T_set | T_signature | T_string | T_timestamp
    | T_unit | T_bls12_381_fr | T_bls12_381_g1 | T_bls12_381_g2 | T_ticket ->
        Type_namespace

  let valid_case name =
    let is_lower = function '_' | 'a' .. 'z' -> true | _ -> false in
    let is_upper = function '_' | 'A' .. 'Z' -> true | _ -> false in
    let rec for_all a b f = a > b || (f a && for_all (a + 1) b f) in
    let len = String.length name in
    len <> 0
    && name.[0] <> '_'
    && ((is_upper name.[0] && for_all 1 (len - 1) (fun i -> is_upper name.[i]))
       || (is_upper name.[0] && for_all 1 (len - 1) (fun i -> is_lower name.[i]))
       || (is_lower name.[0] && for_all 1 (len - 1) (fun i -> is_lower name.[i]))
       )

  let string_of_prim = function
    | K_parameter -> "parameter"
    | K_storage -> "storage"
    | K_code -> "code"
    | D_False -> "False"
    | D_Elt -> "Elt"
    | D_Left -> "Left"
    | D_None -> "None"
    | D_Pair -> "Pair"
    | D_Right -> "Right"
    | D_Some -> "Some"
    | D_True -> "True"
    | D_Unit -> "Unit"
    | I_PACK -> "PACK"
    | I_UNPACK -> "UNPACK"
    | I_BLAKE2B -> "BLAKE2B"
    | I_SHA256 -> "SHA256"
    | I_SHA512 -> "SHA512"
    | I_ABS -> "ABS"
    | I_ADD -> "ADD"
    | I_AMOUNT -> "AMOUNT"
    | I_AND -> "AND"
    | I_BALANCE -> "BALANCE"
    | I_CAR -> "CAR"
    | I_CDR -> "CDR"
    | I_CHAIN_ID -> "CHAIN_ID"
    | I_CHECK_SIGNATURE -> "CHECK_SIGNATURE"
    | I_COMPARE -> "COMPARE"
    | I_CONCAT -> "CONCAT"
    | I_CONS -> "CONS"
    | I_CREATE_ACCOUNT -> "CREATE_ACCOUNT"
    | I_CREATE_CONTRACT -> "CREATE_CONTRACT"
    | I_IMPLICIT_ACCOUNT -> "IMPLICIT_ACCOUNT"
    | I_DIP -> "DIP"
    | I_DROP -> "DROP"
    | I_DUP -> "DUP"
    | I_EDIV -> "EDIV"
    | I_EMPTY_BIG_MAP -> "EMPTY_BIG_MAP"
    | I_EMPTY_MAP -> "EMPTY_MAP"
    | I_EMPTY_SET -> "EMPTY_SET"
    | I_EQ -> "EQ"
    | I_EXEC -> "EXEC"
    | I_APPLY -> "APPLY"
    | I_FAILWITH -> "FAILWITH"
    | I_GE -> "GE"
    | I_GET -> "GET"
    | I_GET_AND_UPDATE -> "GET_AND_UPDATE"
    | I_GT -> "GT"
    | I_HASH_KEY -> "HASH_KEY"
    | I_IF -> "IF"
    | I_IF_CONS -> "IF_CONS"
    | I_IF_LEFT -> "IF_LEFT"
    | I_IF_NONE -> "IF_NONE"
    | I_INT -> "INT"
    | I_LAMBDA -> "LAMBDA"
    | I_LE -> "LE"
    | I_LEFT -> "LEFT"
    | I_LEVEL -> "LEVEL"
    | I_LOOP -> "LOOP"
    | I_LSL -> "LSL"
    | I_LSR -> "LSR"
    | I_LT -> "LT"
    | I_MAP -> "MAP"
    | I_MEM -> "MEM"
    | I_MUL -> "MUL"
    | I_NEG -> "NEG"
    | I_NEQ -> "NEQ"
    | I_NIL -> "NIL"
    | I_NONE -> "NONE"
    | I_NOT -> "NOT"
    | I_NOW -> "NOW"
    | I_OR -> "OR"
    | I_PAIR -> "PAIR"
    | I_PUSH -> "PUSH"
    | I_RIGHT -> "RIGHT"
    | I_SIZE -> "SIZE"
    | I_SOME -> "SOME"
    | I_SOURCE -> "SOURCE"
    | I_SENDER -> "SENDER"
    | I_SELF -> "SELF"
    | I_SELF_ADDRESS -> "SELF_ADDRESS"
    | I_SLICE -> "SLICE"
    | I_STEPS_TO_QUOTA -> "STEPS_TO_QUOTA"
    | I_SUB -> "SUB"
    | I_SWAP -> "SWAP"
    | I_TRANSFER_TOKENS -> "TRANSFER_TOKENS"
    | I_SET_DELEGATE -> "SET_DELEGATE"
    | I_UNIT -> "UNIT"
    | I_UNPAIR -> "UNPAIR"
    | I_UPDATE -> "UPDATE"
    | I_XOR -> "XOR"
    | I_ITER -> "ITER"
    | I_LOOP_LEFT -> "LOOP_LEFT"
    | I_ADDRESS -> "ADDRESS"
    | I_CONTRACT -> "CONTRACT"
    | I_ISNAT -> "ISNAT"
    | I_CAST -> "CAST"
    | I_RENAME -> "RENAME"
    | I_SAPLING_EMPTY_STATE -> "SAPLING_EMPTY_STATE"
    | I_SAPLING_VERIFY_UPDATE -> "SAPLING_VERIFY_UPDATE"
    | I_DIG -> "DIG"
    | I_DUG -> "DUG"
    | I_NEVER -> "NEVER"
    | I_VOTING_POWER -> "VOTING_POWER"
    | I_TOTAL_VOTING_POWER -> "TOTAL_VOTING_POWER"
    | I_KECCAK -> "KECCAK"
    | I_SHA3 -> "SHA3"
    | I_PAIRING_CHECK -> "PAIRING_CHECK"
    | I_TICKET -> "TICKET"
    | I_READ_TICKET -> "READ_TICKET"
    | I_SPLIT_TICKET -> "SPLIT_TICKET"
    | I_JOIN_TICKETS -> "JOIN_TICKETS"
    | T_bool -> "bool"
    | T_contract -> "contract"
    | T_int -> "int"
    | T_key -> "key"
    | T_key_hash -> "key_hash"
    | T_lambda -> "lambda"
    | T_list -> "list"
    | T_map -> "map"
    | T_big_map -> "big_map"
    | T_nat -> "nat"
    | T_option -> "option"
    | T_or -> "or"
    | T_pair -> "pair"
    | T_set -> "set"
    | T_signature -> "signature"
    | T_string -> "string"
    | T_bytes -> "bytes"
    | T_mutez -> "mutez"
    | T_timestamp -> "timestamp"
    | T_unit -> "unit"
    | T_operation -> "operation"
    | T_address -> "address"
    | T_sapling_state -> "sapling_state"
    | T_sapling_transaction -> "sapling_transaction"
    | T_chain_id -> "chain_id"
    | T_never -> "never"
    | T_bls12_381_g1 -> "bls12_381_g1"
    | T_bls12_381_g2 -> "bls12_381_g2"
    | T_bls12_381_fr -> "bls12_381_fr"
    | T_ticket -> "ticket"

  let prim_encoding =
    let open Data_encoding in
    def "michelson.v1.primitives"
    @@ string_enum
         (* Add the comment below every 10 lines *)
         [ (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("parameter", K_parameter);
           ("storage", K_storage);
           ("code", K_code);
           ("False", D_False);
           ("Elt", D_Elt);
           ("Left", D_Left);
           ("None", D_None);
           ("Pair", D_Pair);
           ("Right", D_Right);
           ("Some", D_Some);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("True", D_True);
           ("Unit", D_Unit);
           ("PACK", I_PACK);
           ("UNPACK", I_UNPACK);
           ("BLAKE2B", I_BLAKE2B);
           ("SHA256", I_SHA256);
           ("SHA512", I_SHA512);
           ("ABS", I_ABS);
           ("ADD", I_ADD);
           ("AMOUNT", I_AMOUNT);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("AND", I_AND);
           ("BALANCE", I_BALANCE);
           ("CAR", I_CAR);
           ("CDR", I_CDR);
           ("CHECK_SIGNATURE", I_CHECK_SIGNATURE);
           ("COMPARE", I_COMPARE);
           ("CONCAT", I_CONCAT);
           ("CONS", I_CONS);
           ("CREATE_ACCOUNT", I_CREATE_ACCOUNT);
           ("CREATE_CONTRACT", I_CREATE_CONTRACT);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("IMPLICIT_ACCOUNT", I_IMPLICIT_ACCOUNT);
           ("DIP", I_DIP);
           ("DROP", I_DROP);
           ("DUP", I_DUP);
           ("EDIV", I_EDIV);
           ("EMPTY_MAP", I_EMPTY_MAP);
           ("EMPTY_SET", I_EMPTY_SET);
           ("EQ", I_EQ);
           ("EXEC", I_EXEC);
           ("FAILWITH", I_FAILWITH);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("GE", I_GE);
           ("GET", I_GET);
           ("GT", I_GT);
           ("HASH_KEY", I_HASH_KEY);
           ("IF", I_IF);
           ("IF_CONS", I_IF_CONS);
           ("IF_LEFT", I_IF_LEFT);
           ("IF_NONE", I_IF_NONE);
           ("INT", I_INT);
           ("LAMBDA", I_LAMBDA);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("LE", I_LE);
           ("LEFT", I_LEFT);
           ("LOOP", I_LOOP);
           ("LSL", I_LSL);
           ("LSR", I_LSR);
           ("LT", I_LT);
           ("MAP", I_MAP);
           ("MEM", I_MEM);
           ("MUL", I_MUL);
           ("NEG", I_NEG);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("NEQ", I_NEQ);
           ("NIL", I_NIL);
           ("NONE", I_NONE);
           ("NOT", I_NOT);
           ("NOW", I_NOW);
           ("OR", I_OR);
           ("PAIR", I_PAIR);
           ("PUSH", I_PUSH);
           ("RIGHT", I_RIGHT);
           ("SIZE", I_SIZE);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("SOME", I_SOME);
           ("SOURCE", I_SOURCE);
           ("SENDER", I_SENDER);
           ("SELF", I_SELF);
           ("STEPS_TO_QUOTA", I_STEPS_TO_QUOTA);
           ("SUB", I_SUB);
           ("SWAP", I_SWAP);
           ("TRANSFER_TOKENS", I_TRANSFER_TOKENS);
           ("SET_DELEGATE", I_SET_DELEGATE);
           ("UNIT", I_UNIT);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("UPDATE", I_UPDATE);
           ("XOR", I_XOR);
           ("ITER", I_ITER);
           ("LOOP_LEFT", I_LOOP_LEFT);
           ("ADDRESS", I_ADDRESS);
           ("CONTRACT", I_CONTRACT);
           ("ISNAT", I_ISNAT);
           ("CAST", I_CAST);
           ("RENAME", I_RENAME);
           ("bool", T_bool);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("contract", T_contract);
           ("int", T_int);
           ("key", T_key);
           ("key_hash", T_key_hash);
           ("lambda", T_lambda);
           ("list", T_list);
           ("map", T_map);
           ("big_map", T_big_map);
           ("nat", T_nat);
           ("option", T_option);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("or", T_or);
           ("pair", T_pair);
           ("set", T_set);
           ("signature", T_signature);
           ("string", T_string);
           ("bytes", T_bytes);
           ("mutez", T_mutez);
           ("timestamp", T_timestamp);
           ("unit", T_unit);
           ("operation", T_operation);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           ("address", T_address);
           (* Alpha_002 addition *)
           ("SLICE", I_SLICE);
           (* Alpha_005 addition *)
           ("DIG", I_DIG);
           ("DUG", I_DUG);
           ("EMPTY_BIG_MAP", I_EMPTY_BIG_MAP);
           ("APPLY", I_APPLY);
           ("chain_id", T_chain_id);
           ("CHAIN_ID", I_CHAIN_ID);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           (* Alpha_008 addition *)
           ("LEVEL", I_LEVEL);
           ("SELF_ADDRESS", I_SELF_ADDRESS);
           ("never", T_never);
           ("NEVER", I_NEVER);
           ("UNPAIR", I_UNPAIR);
           ("VOTING_POWER", I_VOTING_POWER);
           ("TOTAL_VOTING_POWER", I_TOTAL_VOTING_POWER);
           ("KECCAK", I_KECCAK);
           ("SHA3", I_SHA3);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           (* Alpha_008 addition *)
           ("PAIRING_CHECK", I_PAIRING_CHECK);
           ("bls12_381_g1", T_bls12_381_g1);
           ("bls12_381_g2", T_bls12_381_g2);
           ("bls12_381_fr", T_bls12_381_fr);
           ("sapling_state", T_sapling_state);
           ("sapling_transaction", T_sapling_transaction);
           ("SAPLING_EMPTY_STATE", I_SAPLING_EMPTY_STATE);
           ("SAPLING_VERIFY_UPDATE", I_SAPLING_VERIFY_UPDATE);
           ("ticket", T_ticket);
           (* /!\ NEW INSTRUCTIONS MUST BE ADDED AT THE END OF THE STRING_ENUM, FOR BACKWARD COMPATIBILITY OF THE ENCODING. *)
           (* Alpha_008 addition *)
           ("TICKET", I_TICKET);
           ("READ_TICKET", I_READ_TICKET);
           ("SPLIT_TICKET", I_SPLIT_TICKET);
           ("JOIN_TICKETS", I_JOIN_TICKETS);
           ("GET_AND_UPDATE", I_GET_AND_UPDATE)
           (* New instructions must be added here, for backward compatibility of the encoding. *)
           (* Keep the comment above at the end of the list *) ]
end

module Micheline_size = struct
  module S = Int

  type t = { nodes : S.t; string_bytes : S.t; z_bytes : S.t }

  let make ~nodes ~string_bytes ~z_bytes = { nodes; string_bytes; z_bytes }

  let zero = { nodes = S.zero; string_bytes = S.zero; z_bytes = S.zero }

  let add_int acc n =
    let numbits = Z.numbits n in
    let z_bytes =
      (numbits + 7) / 8
      (* Compute the number of bytes in a Z.t *)
    in
    { nodes = S.succ acc.nodes;
      string_bytes = acc.string_bytes;
      z_bytes = S.add acc.z_bytes z_bytes
    }

  let add_string acc n =
    let string_bytes = String.length n in
    { nodes = S.succ acc.nodes;
      string_bytes = S.add acc.string_bytes string_bytes;
      z_bytes = acc.z_bytes
    }

  let add_bytes acc n =
    let string_bytes = Bytes.length n in
    { nodes = S.succ acc.nodes;
      string_bytes = S.add acc.string_bytes string_bytes;
      z_bytes = acc.z_bytes
    }

  let add_node s = { s with nodes = S.succ s.nodes }

  (* We model annotations as Seqs of Strings *)
  let of_annots acc annots =
    List.fold_left (fun acc s -> add_string acc s) acc annots

  let rec of_nodes acc nodes more_nodes =
    let open Micheline in
    match nodes with
    | [] -> (
        match more_nodes with
        | [] -> acc
        | nodes :: more_nodes ->
            (of_nodes [@ocaml.tailcall]) acc nodes more_nodes)
    | Int (_, n) :: nodes ->
        let acc = add_int acc n in
        (of_nodes [@ocaml.tailcall]) acc nodes more_nodes
    | String (_, s) :: nodes ->
        let acc = add_string acc s in
        (of_nodes [@ocaml.tailcall]) acc nodes more_nodes
    | Bytes (_, s) :: nodes ->
        let acc = add_bytes acc s in
        (of_nodes [@ocaml.tailcall]) acc nodes more_nodes
    | Prim (_, _, args, annots) :: nodes ->
        let acc = add_node acc in
        let acc = of_annots acc annots in
        (of_nodes [@ocaml.tailcall]) acc args (nodes :: more_nodes)
    | Seq (_, args) :: nodes ->
        let acc = add_node acc in
        (of_nodes [@ocaml.tailcall]) acc args (nodes :: more_nodes)

  let of_node node = of_nodes zero [node] []

  let dot_product s1 s2 =
    S.add
      (S.mul s1.nodes s2.nodes)
      (S.add
         (S.mul s1.string_bytes s2.string_bytes)
         (S.mul s1.z_bytes s2.z_bytes))
end

(* let upper_bound = 32_768 *)
let upper_bound = 1024

let ns () = 1e9 *. Unix.gettimeofday () [@@inline]

let mean_time ~nsamples f =
  let tot = ref 0.0 in
  for _ = 1 to nsamples do
    let start = ns () in
    f () ;
    let stop = ns () in
    tot := !tot +. (stop -. start)
  done ;
  !tot /. float nsamples

let encoding = Micheline.canonical_encoding ~variant:"" Prim.prim_encoding

let rng_state = Random.State.make [| 0x1337; 0x533D; 0x1312 |]

let explore ~playouts initial =
  let rec explore state =
    match state with
    | MCTS_state.Terminal Cut -> Format.printf "result: cut (0.0)@."
    | MCTS_state.Terminal (Leaf (enc, v, reward)) ->
        let bytes = Data_encoding.Binary.to_bytes_exn enc v in
        (* Proper way: encde v to bytes using enc, decode with proper encoding *)
        let v : Prim.prim Micheline.canonical =
          Data_encoding.Binary.of_bytes_exn encoding bytes
        in
        Printer.print_expr
          Format.std_formatter
          (Printer.printable Prim.string_of_prim v) ;
        Format.printf "@." ;
        Format.printf "ns: %f@." reward ;
        Format.printf "len: %d@." (Bytes.length bytes) ;
        Format.printf "ns/byte: %f@." (reward /. float (Bytes.length bytes))
    | MCTS_state.Nonterminal nt ->
        let action = MCTS.policy ~playouts nt rng_state in
        explore (MCTS_state.next nt action)
  in
  explore initial

let maximize_number_of_nodes =
  MCTS_state.make encoding (fun term ->
      match Data_encoding.Binary.to_bytes_exn encoding term with
      | bytes ->
          let len = Bytes.length bytes in
          if len > upper_bound then 0.0
          else
            let size = Micheline_size.of_node (Micheline.root term) in
            float size.nodes)

let () = explore ~playouts:10_000 maximize_number_of_nodes

let maximize_serialization_time =
  MCTS_state.make encoding (fun term ->
      let dt =
        mean_time ~nsamples:1000 (fun () ->
            ignore (Data_encoding.Binary.to_bytes_exn encoding term))
      in
      match Data_encoding.Binary.to_bytes_exn encoding term with
      | bytes ->
          let len = Bytes.length bytes in
          if len > upper_bound then 0.0
          else if len = 0 then assert false
          else dt)

let () = explore ~playouts:1_000_000 maximize_serialization_time
