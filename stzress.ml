(* Copyright Nomadic Labs, 2021, MIT License *)
let numbits_table =
  "\000\001\002\002\003\003\003\003\004\004\004\004\004\004\004\004\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\005\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\006\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\007\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008\008"

(* Copyright Nomadic Labs, 2021, MIT License *)
let numbits x =
  let x = ref x and n = ref 0 in
  (let y = (!x lsr 16) lsr 16 in
   if y <> 0 then (
     n := !n + 32 ;
     x := y)) ;
  (let y = !x lsr 16 in
   if y <> 0 then (
     n := !n + 16 ;
     x := y)) ;
  (let y = !x lsr 8 in
   if y <> 0 then (
     n := !n + 8 ;
     x := y)) ;
  !n + Char.code numbits_table.[!x]

(* Copyright Nomadic Labs, 2021, MIT License *)
let ( -- ) i j = List.init (j - i + 1) (fun x -> x + i)

let pow2 n = if n < 0 then invalid_arg "pow2" else 1 lsl n

let pow2_64 n = if n < 0 then invalid_arg "pow2_64" else Int64.shift_left 1L n

let pow2_z n = if n < 0 then invalid_arg "pow2_z" else Z.pow (Z.of_int 2) n

(* Return a list of numbers of each bitwidth <= [numbits]  *)
let bitwidths_below_that_of ~numbits =
  assert (numbits >= 0) ;
  List.map (fun i -> pow2 i - 1) (0 -- numbits)

(* Return a list of numbers of each bitwidth <= [numbits]  *)
let bitwidths_below_that_of_64 ~numbits =
  assert (numbits >= 0) ;
  List.map (fun i -> Int64.sub (pow2_64 i) 1L) (0 -- numbits)

(* Return a list of numbers of each bytewidth <= [numbytes]  *)
let words_below_that_of_z ~numwords =
  assert (numwords >= 0) ;
  List.map (fun i -> Z.sub (pow2_z (i * 64)) Z.one) (0 -- numwords)

(* split the interval [0,n] in [card] evenly spaced elements  *)
let evenly_spaced ~card n =
  if n < 0 then invalid_arg "evenly_spaced" ;
  if card <= 1 then invalid_arg "evenly_spaced" ;
  if card > n + 1 then invalid_arg "evenly_spaced" ;
  let rec loop delta i acc =
    if i > n then acc else loop delta (i + delta) (i :: acc)
  in
  let delta = n / (card - 1) in
  assert (delta > 0) ;
  loop delta 0 []

let with_neg l = List.sort_uniq Int.compare (List.map ( ~- ) l @ l)

let with_neg_64 l = List.sort_uniq Int64.compare (List.map Int64.neg l @ l)

let with_neg_z l = List.sort_uniq Z.compare (List.map Z.neg l @ l)

module Parameters = struct
  let array_max_size = 1024

  let max_bytes_length = 1024

  let max_string_length = 255
end

type 'a t = 'a Data_encoding__Encoding.t

type terminal = Cut : terminal | Leaf : 'a t * 'a * float -> terminal

module MCTS_state : sig
  include Mcts.S with type terminal = terminal

  val make : 'a t -> ('a -> float) -> state
end = struct
  type nonrec terminal = terminal

  type nonterminal = Ex_nt : 'a t * (unit -> state) array -> nonterminal

  and state = Terminal of terminal | Nonterminal of nonterminal

  type action = unit -> state

  let terminal r = Terminal r

  let nonterminal enc actions = Nonterminal (Ex_nt (enc, actions))

  module Nonterminal = struct
    let unit enc reward =
      let actions = [| (fun () -> reward ()) |] in
      nonterminal enc actions

    let int ints (enc : int t) reward =
      let actions = Array.map (fun i () -> reward i) ints in
      nonterminal enc actions

    let bool enc reward =
      let actions = [| (fun () -> reward false); (fun () -> reward true) |] in
      nonterminal enc actions

    let int8 =
      let ints =
        Array.of_list @@ with_neg @@ bitwidths_below_that_of ~numbits:7
      in
      fun enc reward -> int ints enc reward

    let uint8 =
      let ints = Array.of_list @@ bitwidths_below_that_of ~numbits:8 in
      fun enc reward -> int ints enc reward

    let int16 =
      let ints =
        Array.of_list @@ with_neg @@ bitwidths_below_that_of ~numbits:15
      in
      fun enc reward -> int ints enc reward

    let uint16 =
      let ints = Array.of_list @@ bitwidths_below_that_of ~numbits:16 in
      fun enc reward -> int ints enc reward

    let int31 =
      let ints =
        Array.of_list @@ with_neg @@ bitwidths_below_that_of ~numbits:30
      in
      fun enc reward -> int ints enc reward

    let int32 =
      let ints =
        Array.of_list
        @@ List.map
             Int32.of_int
             (with_neg (bitwidths_below_that_of ~numbits:31))
      in
      fun (enc : int32 t) reward ->
        let actions = Array.map (fun i () -> reward i) ints in
        nonterminal enc actions

    let int64 =
      let ints =
        Array.of_list @@ with_neg_64 (bitwidths_below_that_of_64 ~numbits:62)
      in
      fun (enc : int64 t) reward ->
        let actions = Array.map (fun i () -> reward i) ints in
        nonterminal enc actions

    let n =
      let ints = Array.of_list @@ words_below_that_of_z ~numwords:16 in
      fun (enc : Z.t t) reward ->
        let actions = Array.map (fun i () -> reward i) ints in
        nonterminal enc actions

    let z =
      let ints =
        Array.of_list @@ with_neg_z @@ words_below_that_of_z ~numwords:16
      in
      fun (enc : Z.t t) reward ->
        let actions = Array.map (fun i () -> reward i) ints in
        nonterminal enc actions
  end

  let rec make : type a. a t -> (a -> state) -> state =
    fun (type a) (enc : a t) (reward : a -> state) ->
     match enc.encoding with
     | Data_encoding__Encoding.Null -> Nonterminal.unit enc reward
     | Data_encoding__Encoding.Empty -> Nonterminal.unit enc reward
     | Data_encoding__Encoding.Ignore -> Nonterminal.unit enc reward
     | Data_encoding__Encoding.Constant _s -> Nonterminal.unit enc reward
     | Data_encoding__Encoding.Bool -> Nonterminal.bool enc reward
     | Data_encoding__Encoding.Int8 -> Nonterminal.int8 enc reward
     | Data_encoding__Encoding.Uint8 -> Nonterminal.uint8 enc reward
     | Data_encoding__Encoding.Int16 -> Nonterminal.int16 enc reward
     | Data_encoding__Encoding.Uint16 -> Nonterminal.uint16 enc reward
     | Data_encoding__Encoding.Int31 -> Nonterminal.int31 enc reward
     | Data_encoding__Encoding.Int32 -> Nonterminal.int32 enc reward
     | Data_encoding__Encoding.Int64 -> Nonterminal.int64 enc reward
     | Data_encoding__Encoding.N -> Nonterminal.n enc reward
     | Data_encoding__Encoding.Z -> Nonterminal.z enc reward
     | Data_encoding__Encoding.RangedInt { minimum; maximum } ->
         let actions =
           [| (fun () -> reward minimum); (fun () -> reward maximum) |]
         in
         nonterminal enc actions
     | Data_encoding__Encoding.RangedFloat { minimum; maximum } ->
         let actions =
           [| (fun () -> reward minimum); (fun () -> reward maximum) |]
         in
         nonterminal enc actions
     | Data_encoding__Encoding.Float ->
         let actions =
           [| (fun () -> reward min_float); (fun () -> reward max_float) |]
         in
         nonterminal enc actions
     | Data_encoding__Encoding.Bytes (`Fixed length) ->
         let bytes = Bytes.create length in
         let actions = [| (fun () -> reward bytes) |] in
         nonterminal enc actions
     | Data_encoding__Encoding.Bytes `Variable ->
         let lengths =
           evenly_spaced
             ~card:(numbits Parameters.max_bytes_length)
             Parameters.max_bytes_length
         in
         let actions =
           Array.of_list
             (List.map
                (fun len () ->
                  let bytes = Bytes.create len in
                  reward bytes)
                lengths)
         in
         nonterminal enc actions
     | Data_encoding__Encoding.String (`Fixed length) ->
         let string = String.make length 'a' in
         let actions = [| (fun () -> reward string) |] in
         nonterminal enc actions
     | Data_encoding__Encoding.String `Variable ->
         let lengths =
           evenly_spaced
             ~card:(numbits Parameters.max_string_length)
             Parameters.max_string_length
         in
         let actions =
           Array.of_list
             (List.map
                (fun len () ->
                  let str = String.make len 'a' in
                  reward str)
                lengths)
         in
         nonterminal enc actions
     | Data_encoding__Encoding.Padded (enc, _) -> make enc reward
     | Data_encoding__Encoding.String_enum (_table, arr) ->
         let actions = Array.map (fun v () -> reward v) arr in
         nonterminal enc actions
     | Data_encoding__Encoding.Array (max_size_opt, venc) ->
         let max_length =
           Option.fold
             ~none:Parameters.array_max_size
             ~some:(fun len -> min len Parameters.array_max_size)
             max_size_opt
         in
         assert (max_length >= 0) ;
         let lengths =
           if max_length = 0 then [0]
           else evenly_spaced ~card:(numbits max_length) max_length
         in
         let actions =
           Array.of_list
             (List.map (fun len () -> make_array len venc reward) lengths)
         in
         nonterminal enc actions
     | Data_encoding__Encoding.List (max_size_opt, venc) ->
         let max_length =
           Option.fold
             ~none:Parameters.array_max_size
             ~some:(fun len -> min len Parameters.array_max_size)
             max_size_opt
         in
         assert (max_length >= 0) ;
         let lengths =
           if max_length = 0 then [0]
           else evenly_spaced ~card:(numbits max_length) max_length
         in
         let actions =
           Array.of_list
             (List.map (fun len () -> make_list len venc reward) lengths)
         in
         nonterminal enc actions
     | Data_encoding__Encoding.Obj field -> (
         match field with
         | Data_encoding__Encoding.Req { encoding; _ } -> make encoding reward
         | Data_encoding__Encoding.Opt { encoding; _ } ->
             let actions =
               [| (fun () -> reward Option.none);
                  (fun () -> make encoding (fun v -> reward (Option.some v)))
               |]
             in
             nonterminal enc actions
         | Data_encoding__Encoding.Dft { encoding; default; _ } ->
             let actions =
               [| (fun () -> reward default);
                  (fun () -> make encoding reward)
               |]
             in
             nonterminal enc actions)
     | Data_encoding__Encoding.Objs { left; right; _ } ->
         make left @@ fun l ->
         make right @@ fun r -> reward (l, r)
     | Data_encoding__Encoding.Tup enc -> make enc reward
     | Data_encoding__Encoding.Tups { left; right; _ } ->
         make left @@ fun l ->
         make right @@ fun r -> reward (l, r)
     | Data_encoding__Encoding.Union { cases; _ } ->
         let cases =
           Array.of_list
           @@ List.map
                (function
                  | Data_encoding__Encoding.Case { title = _; encoding; inj; _ }
                    ->
                      fun () -> make encoding (fun v -> reward (inj v)))
                cases
         in
         nonterminal enc cases
     | Data_encoding__Encoding.Mu { fix; _ } -> make (fix enc) reward
     | Data_encoding__Encoding.Conv { inj; encoding; _ } ->
         make encoding (fun v ->
             (* handle partial [conv]s... *)
             try reward (inj v) with _exn -> Terminal Cut)
     | Data_encoding__Encoding.Describe { encoding; _ } -> make encoding reward
     | Data_encoding__Encoding.Splitted { encoding; _ } -> make encoding reward
     | Data_encoding__Encoding.Dynamic_size { encoding; _ } ->
         make encoding reward
     | Data_encoding__Encoding.Check_size { limit = _; encoding } ->
         make encoding reward
     | Data_encoding__Encoding.Delayed f -> make (f ()) reward

  and make_array : type a. int -> a t -> (a array -> state) -> state =
   fun len venc reward -> make_list len venc (fun l -> reward (Array.of_list l))

  and make_list : type a. int -> a t -> (a list -> state) -> state =
   fun len venc reward ->
    let rec loop n acc =
      if n = 0 then reward acc else make venc (fun v -> loop (n - 1) (v :: acc))
    in
    loop len []

  let make enc reward = make enc (fun x -> terminal (Leaf (enc, x, reward x)))

  let actions (Ex_nt (_, actions)) = actions

  let next _nt action = action ()

  let reward (x : terminal) =
    match x with Cut -> 0.0 | Leaf (_, _, reward) -> reward

  let exploration_depth = `Bounded 10_000_000

  let exploration_kernel = `Uniform

  let pp_action fmtr _ = Format.pp_print_string fmtr "action"

  let pp_terminal fmtr _ = Format.pp_print_string fmtr "terminal"

  let pp_nonterminal fmtr _ = Format.pp_print_string fmtr "nonterminal"
end

module MCTS = Mcts.MCTS (MCTS_state)
