open Utils
open Ast
open Ustring.Op

module UstringSet = Set.Make(Ustring)

(* This is taken from Core: https://github.com/monadbobo/ocaml-core/blob/9c1c06e7a1af7e15b6019a325d7dbdbd4cdb4020/base/core/lib/core_list.ml#L566-L571 *)
let concat_map l ~f =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl -> aux (List.rev_append (f hd) acc) tl
  in
  aux [] l

let rec split_at n = function
  | x :: xs when n > 0 ->
     let (pre, post) = split_at (n-1) xs
     in (x :: pre, post)
  | l -> ([], l)

let repeat (n: int) (v: 'a): 'a list = List.init n (fun _ -> v)

(* TODO(vipa): make lists and records similar, put both constructors here, move what's in the negative pattern to edge pattern for sequences, add an exact record pattern *)
type simple_con =
| IntCon of int
| CharCon of int
| BoolCon of bool
| ConCon of ustring
| RecCon

module SimpleConOrd = struct
  type t = simple_con
  (* NOTE(?,?): I can't just use the polymorphic compare in the standard library
   * since ustring has internal mutation that would be visible to it, but
   * shouldn't affect the result *)
  let compare a b = match a, b with
    | IntCon a, IntCon b -> Int.compare a b
    | CharCon a, CharCon b -> Int.compare a b
    | BoolCon a, BoolCon b -> Bool.compare a b
    | ConCon a, ConCon b -> Ustring.compare a b
    | RecCon, RecCon -> 0
    | IntCon _, (CharCon _ | BoolCon _ | ConCon _ | RecCon) -> -1
    | (CharCon _ | BoolCon _ | ConCon _ | RecCon), IntCon _  -> 1
    | CharCon _, (BoolCon _ | ConCon _ | RecCon) -> -1
    | (BoolCon _ | ConCon _ | RecCon), CharCon _  -> 1
    | BoolCon _, (ConCon _ | RecCon) -> -1
    | (ConCon _ | RecCon), BoolCon _ -> 1
    | ConCon _, RecCon -> -1
    | RecCon, ConCon _ -> 1
end
module ConSet = Set.Make(SimpleConOrd)

type simple_pat =
| SPatInt of int
| SPatChar of int
| SPatBool of bool
| SPatCon of ustring * npat
and npat =
| NSPat of simple_pat
| NPatRecord of npat Record.t * UstringSet.t (* The set is disallowed labels *)
| NPatSeqTot of npat list
| NPatSeqEdg of npat list * npat list
| NPatNot
  of IntSet.t option (* Some lengths -> the disallowed sequence lengths, None -> no sequences allowed *)
     * ConSet.t (* The disallowed simple constructors *)
let wildpat = NPatNot (Some IntSet.empty, ConSet.empty)
let notpat_simple c = NPatNot (Some IntSet.empty, ConSet.singleton c)
let notpat_seq_len n = NPatNot (Some (IntSet.singleton n), ConSet.empty)
let notpat_seq = NPatNot (None, ConSet.empty)

let simple_con_of_simple_pat = function
  | SPatInt i -> IntCon i
  | SPatChar c -> CharCon c
  | SPatBool b -> BoolCon b
  | SPatCon (c, _) -> ConCon c

module NPatOrd = struct
  type t = npat
  let rec compare_list a b = match a, b with
    | [], [] -> 0
    | x::xs, y::ys ->
       let pat_res = compare x y in
       if pat_res = 0 then compare_list xs ys else pat_res
    | [], _::_ -> -1
    | _::_, [] -> 1
  and compare_simple a b = match a, b with
    | SPatInt a, SPatInt b -> Int.compare a b
    | SPatChar a, SPatChar b -> Int.compare a b
    | SPatBool a, SPatBool b -> Bool.compare a b
    | SPatCon (str1, p1), SPatCon (str2, p2) ->
       let str_res = Ustring.compare str1 str2 in
       if str_res = 0 then compare p1 p2 else str_res
    | SPatInt _, (SPatChar _ | SPatBool _ | SPatCon _) -> -1
    | (SPatChar _ | SPatBool _ | SPatCon _), SPatInt _  -> 1
    | SPatChar _, (SPatBool _ | SPatCon _) -> -1
    | (SPatBool _ | SPatCon _), SPatChar _ -> 1
    | SPatBool _, SPatCon _ -> -1
    | SPatCon _, SPatBool _ -> -1
  and compare a b = match a, b with
    | NSPat a, NSPat b -> compare_simple a b
    | NPatRecord (a1, d1), NPatRecord (a2, d2) ->
       let rec_res = Record.compare compare a1 a2 in
       if rec_res = 0 then UstringSet.compare d1 d2 else rec_res
    | NPatSeqTot a, NPatSeqTot b -> compare_list a b
    | NPatSeqEdg (pre1, post1), NPatSeqEdg (pre2, post2) ->
       let pre_res = compare_list pre1 pre2 in
       if pre_res = 0 then compare_list post1 post2 else pre_res
    | NPatNot (seqs1, cons1), NPatNot (seqs2, cons2) ->
       let seq_res = Option.compare ~cmp:IntSet.compare seqs1 seqs2 in
       if seq_res <> 0 then seq_res else
       ConSet.compare cons1 cons2
    | NSPat _, (NPatRecord _ | NPatSeqTot _ | NPatSeqEdg _ | NPatNot _) -> -1
    | (NPatRecord _ | NPatSeqTot _ | NPatSeqEdg _ | NPatNot _), NSPat _ -> 1
    | NPatRecord _, (NPatSeqTot _ | NPatSeqEdg _ | NPatNot _) -> -1
    | (NPatSeqTot _ | NPatSeqEdg _ | NPatNot _), NPatRecord _ -> 1
    | NPatSeqTot _, (NPatSeqEdg _ | NPatNot _) -> -1
    | (NPatSeqEdg _ | NPatNot _), NPatSeqTot _ -> 1
    | NPatSeqEdg _, NPatNot _ -> -1
    | NPatNot _, NPatSeqEdg _ -> -1
end
module NPatSet = Set.Make(NPatOrd)

type normpat = NPatSet.t

let traverse (f : 'a -> 'b list) (l : 'a list): 'b list list =
  let rec go = function
    | [] -> [[]]
    | x :: xs ->
       let tails = go xs in
       let heads = f x in
       concat_map tails ~f:(fun tl -> List.map (fun hd -> hd::tl) heads)
  in go l

let liftA2 (f: 'a -> 'b -> 'c) (la: 'a list) (lb: 'b list): 'c list =
  concat_map la ~f:(fun a -> List.map (f a) lb)

let map2_with_extras (f: 'a -> 'b -> 'c) (extra_a: 'a) (extra_b: 'b): 'a list -> 'b list -> 'c list =
  let rec recur la lb = match la, lb with
    | [], [] -> []
    | [], b :: lb -> f extra_a b :: recur [] lb
    | a :: la, [] -> f a extra_b :: recur la []
    | a :: la, b :: lb -> f a b :: recur la lb
  in recur

let map2_keep_extras (f: 'a -> 'a -> 'b): 'a list -> 'a list -> ((bool * 'a list) option * 'b list) =
  let rec recur la lb = match la, lb with
    | [], [] -> (None, [])
    | [], _::_ -> (Some (true, lb), [])
    | _::_, [] -> (Some (false, la), [])
    | a::la, b::lb ->
       let (extras, res) = recur la lb in
       (extras, f a b :: res)
  in recur

let include_tail (f: 'a -> 'b): ((bool * 'a list) option * 'b list) -> 'b list = function
  | None, pre -> pre
  | Some (_, tail), pre -> pre @ List.map f tail

let rec list_complement (constr: npat list -> npat) (l: npat list): normpat =
  traverse (fun p -> [NPatSet.singleton p; npat_complement p]) l (* Produce all combinations of (complement this) (don't complement this) for each element in the list. Length of this list is thus 2^(length l) *)
  |> List.tl (* Remove the list that doesn't complement anything *)
  (* We now have a normpat list list, where the inner list has length `length l`.
     We want to have a npat list list, where the outermost list will be turned into
     a normpat (after calling constr). We must thus move the multiplicity present in
     normpat (since it's a set) up to the top-most list, which we can do using `traverse`
     in the list monad. *)
  |> concat_map
       ~f:(fun np_list ->
         traverse NPatSet.elements np_list
         |> List.map constr)
  |> NPatSet.of_list (* construct a normpat *)

and npat_complement: npat -> normpat = function
  | NSPat (SPatInt i) -> notpat_simple (IntCon i) |> NPatSet.singleton
  | NSPat (SPatChar c) -> notpat_simple (CharCon c) |> NPatSet.singleton
  | NSPat (SPatBool b) -> notpat_simple (BoolCon b) |> NPatSet.singleton
  | NSPat (SPatCon (c, p)) ->
     npat_complement p
     |> NPatSet.map (fun p -> NSPat (SPatCon (c, p)))
     |> NPatSet.add (notpat_simple (ConCon c))
  | NPatRecord (pats, neg_labels) ->
     let with_forbidden_labels =
       UstringSet.elements neg_labels
       |> List.map (fun label -> NPatRecord (Record.add label wildpat pats, UstringSet.empty))
       |> NPatSet.of_list in
     let (labels, pats) =
       Record.bindings pats
       |> List.split in
     let complemented_product =
       list_complement
         (fun pats ->
           List.combine labels pats
           |> List.to_seq
           |> Record.of_seq
           |> fun x -> NPatRecord (x, UstringSet.empty))
         pats in
     let missing_labels =
       labels
       |> List.map (fun label -> NPatRecord (Record.empty, UstringSet.singleton label))
       |> NPatSet.of_list
     in NPatSet.union complemented_product missing_labels
        |> NPatSet.union with_forbidden_labels
  | NPatSeqTot pats ->
     list_complement (fun pats -> NPatSeqTot pats) pats
     |> NPatSet.add (notpat_seq_len <| List.length pats)
  | NPatSeqEdg (pre, post) ->
     let lenPre, lenPost = List.length pre, List.length post in
     let complemented_product =
       list_complement
         (fun pats -> let pre, post = split_at lenPre pats in NPatSeqEdg(pre, post))
         (pre @ post) in
     let allowed_lengths =
       List.init (lenPre + lenPost)
         (fun n -> NPatSeqTot (repeat n wildpat))
       |> NPatSet.of_list
     in NPatSet.union complemented_product allowed_lengths
        |> NPatSet.add notpat_seq
  | NPatNot (seq_lens, cons) ->
     let seqs = match seq_lens with
       | None -> NPatSeqEdg ([], []) |> NPatSet.singleton
       | Some seq_lens ->
          IntSet.elements seq_lens
          |> List.map (fun n -> NPatSeqTot (repeat n wildpat))
          |> NPatSet.of_list in
     let cons =
       ConSet.elements cons
       |> List.map
            (function
             | IntCon i -> NSPat (SPatInt i)
             | CharCon c -> NSPat (SPatChar c)
             | BoolCon b -> NSPat (SPatBool b)
             | ConCon c -> NSPat (SPatCon (c, wildpat))
             | RecCon -> NPatRecord (Record.empty, UstringSet.empty))
       |> NPatSet.of_list
     in NPatSet.union seqs cons

and npat_intersect (a: npat) (b: npat): normpat = match a, b with
  | NPatNot (seqs1, cons1), NPatNot (seqs2, cons2) ->
     let seqs = match seqs1, seqs2 with
       | None, _ | _, None -> None
       | Some a, Some b -> Some (IntSet.union a b) in
     let cons = ConSet.union cons1 cons2
     in NPatSet.singleton (NPatNot (seqs, cons))
  | NPatNot (_, cons), (NSPat sp as pat) | (NSPat sp as pat), NPatNot (_, cons) ->
     if ConSet.mem (simple_con_of_simple_pat sp) cons
     then NPatSet.empty
     else NPatSet.singleton pat
  | NPatNot (_, cons), (NPatRecord _ as pat)
    | (NPatRecord _ as pat), NPatNot (_, cons) ->
     if ConSet.mem RecCon cons then NPatSet.empty else NPatSet.singleton pat
  | NPatNot (None, _), (NPatSeqTot _ | NPatSeqEdg _)
    | (NPatSeqTot _ | NPatSeqEdg _), NPatNot (None, _) ->
     NPatSet.empty
  | NPatNot (Some lens, _), (NPatSeqTot pats as pat)
    | (NPatSeqTot pats as pat), NPatNot (Some lens, _) ->
    if IntSet.mem (List.length pats) lens then NPatSet.empty else NPatSet.singleton pat
  | NPatNot (Some lens, _), (NPatSeqEdg (pre, post) as pat)
    | (NPatSeqEdg (pre, post) as pat), NPatNot (Some lens, _) ->
     (match IntSet.max_elt_opt lens with
      | None -> NPatSet.singleton pat
      | Some max_forbidden_len ->
         let min_len = List.length pre + List.length post in
         if min_len > max_forbidden_len then NPatSet.singleton pat else
           List.init (max_forbidden_len - min_len) (fun n -> n)
           |> List.filter (fun n -> IntSet.mem (n+min_len) lens |> not)
           |> List.map
                (fun n_extras -> NPatSeqTot (pre @ List.rev_append (repeat n_extras wildpat) post))
           |> NPatSet.of_list
           |> NPatSet.add
                (NPatSeqEdg (pre, List.rev_append (repeat (max_forbidden_len - min_len + 1) wildpat) post)))
  | NSPat p1, NSPat p2 ->
     (match p1, p2 with
      | SPatInt i1, SPatInt i2 when i1 = i2 -> NPatSet.singleton a
      | SPatChar c1, SPatChar c2 when c1 = c2 -> NPatSet.singleton a
      | SPatBool b1, SPatBool b2 when b1 = b2 -> NPatSet.singleton a
      | SPatCon (s1, p1), SPatCon (s2, p2) when s1 = s2 ->
         npat_intersect p1 p2
         |> NPatSet.map (fun p -> NSPat (SPatCon (s1, p)))
      | _ -> NPatSet.empty)
  | NSPat _, (NPatRecord _ | NPatSeqTot _ | NPatSeqEdg _)
    | (NPatRecord _ | NPatSeqTot _ | NPatSeqEdg _), NSPat _ -> NPatSet.empty
  | NPatRecord (r1, neg1), NPatRecord (r2, neg2) ->
     if Record.exists (fun label _ -> UstringSet.mem label neg2) r1
      || Record.exists (fun label _ -> UstringSet.mem label neg1) r2
     then NPatSet.empty
     else
       let neg = UstringSet.union neg1 neg2 in
       let merge_f _ a b = match a, b with
         | None, None -> None
         | Some a, Some b -> Some (npat_intersect a b |> NPatSet.elements)
         | Some a, _ | _, Some a -> Some [a] in
       Record.merge merge_f r1 r2
       |> Record.bindings
       |> traverse (fun (k, vs) -> List.map (fun v -> (k, v)) vs)
       |> List.map (fun bindings -> NPatRecord (List.to_seq bindings |> Record.of_seq, neg))
       |> NPatSet.of_list
  | NPatRecord _, (NPatSeqTot _ | NPatSeqEdg _)
    | (NPatSeqTot _ | NPatSeqEdg _), NPatRecord _ -> NPatSet.empty
  | NPatSeqTot pats1, NPatSeqTot pats2 ->
     if List.length pats1 <> List.length pats2 then NPatSet.empty else
       List.map2 npat_intersect pats1 pats2
       |> traverse NPatSet.elements
       |> List.map (fun pats -> NPatSeqTot pats)
       |> NPatSet.of_list
  | NPatSeqEdg (pre1, post1), NPatSeqEdg (pre2, post2) ->
     let pre = map2_keep_extras npat_intersect pre1 pre2 in
     let rev_post = map2_keep_extras npat_intersect (List.rev post1) (List.rev post2) in
     let simple =
       let pre = include_tail NPatSet.singleton pre in
       let post = List.rev (include_tail NPatSet.singleton rev_post) in
       pre @ post
       |> traverse NPatSet.elements
       |> List.map (fun pats -> let pre, post = split_at (List.length pre) pats in NPatSeqEdg (pre, post))
       |> NPatSet.of_list in
     let overlapping = match pre, rev_post with
       | (Some (pre_dir, pre_extras), pre), (Some (post_dir, rev_post_extras), rev_post)
            when pre_dir <> post_dir ->
          let post = List.rev rev_post in
          let post_extras = List.rev rev_post_extras in
          List.init (List.length pre_extras)
            (fun n -> List.rev_append (repeat n wildpat) post_extras
                      |> map2_with_extras npat_intersect wildpat wildpat pre_extras
                      |> fun mid -> pre @ mid @ post)
          |> concat_map ~f:(traverse NPatSet.elements)
          |> List.map (fun pats -> NPatSeqTot pats)
          |> NPatSet.of_list
       | _ -> NPatSet.empty in
     NPatSet.union simple overlapping
  | NPatSeqEdg (pre, post), NPatSeqTot pats
    | NPatSeqTot pats, NPatSeqEdg (pre, post) ->
     let len_pre, len_post, len_pats = List.length pre, List.length post, List.length pats in
     if len_pre + len_post > len_pats then NPatSet.empty else
       pre @ repeat (len_pats - len_pre - len_post) wildpat @ post
       |> List.map2 npat_intersect pats
       |> traverse NPatSet.elements
       |> List.map (fun pats -> NPatSeqTot pats)
       |> NPatSet.of_list

and normpat_complement (np: normpat): normpat =
  NPatSet.elements np
  |> List.map npat_complement
  |> List.fold_left normpat_intersect (NPatSet.singleton wildpat)

and normpat_intersect (a: normpat) (b: normpat): normpat =
  liftA2 npat_intersect (NPatSet.elements a) (NPatSet.elements b)
  |> List.fold_left NPatSet.union NPatSet.empty

let normpat_subset (a: normpat) (b: normpat): bool =
  normpat_intersect a (normpat_complement b)
  |> NPatSet.is_empty

let normpat_overlap (a: normpat) (b: normpat): bool =
  (* This is a shortcut optimization on normpat_intersect a b |> NPatSet.is_empty |> not,
   * lessening the minimum number of calls to npat_intersect. *)
  liftA2 (fun a b -> (a, b)) (NPatSet.elements a) (NPatSet.elements b)
  |> List.exists (fun (a, b) -> npat_intersect a b |> NPatSet.is_empty |> not)

let rec pat_to_normpat = function
  | PatNamed _ -> NPatSet.singleton wildpat
  | PatSeqTot(_, pats) ->
     Mseq.to_list pats
     |> traverse (fun p -> pat_to_normpat p |> NPatSet.elements)
     |> List.map (fun pats -> NPatSeqTot pats)
     |> NPatSet.of_list
  | PatSeqEdg(_, pre, _, post) ->
     Mseq.concat pre post
     |> Mseq.to_list
     |> traverse (fun p -> pat_to_normpat p |> NPatSet.elements)
     |> List.map (fun pats -> let pre, post = split_at (Mseq.length pre) pats in NPatSeqEdg(pre, post))
     |> NPatSet.of_list
  | PatRecord(_, r) ->
     Record.bindings r
     |> traverse (fun (k, p) ->
            pat_to_normpat p
            |> NPatSet.elements
            |> List.map (fun p -> (k, p)))
     |> List.map (fun bindings -> NPatRecord (List.to_seq bindings |> Record.of_seq, UstringSet.empty))
     |> NPatSet.of_list
  | PatCon(_, c, _, p) ->
     pat_to_normpat p
     |> NPatSet.map (fun p -> NSPat (SPatCon (c, p)))
  | PatInt(_, i) -> NPatSet.singleton (NSPat (SPatInt i))
  | PatChar(_, c) -> NPatSet.singleton (NSPat (SPatChar c))
  | PatBool(_, b) -> NPatSet.singleton (NSPat (SPatBool b))
  | PatAnd(_, a, b) -> normpat_intersect (pat_to_normpat a) (pat_to_normpat b)
  | PatOr(_, a, b) -> NPatSet.union (pat_to_normpat a) (pat_to_normpat b)
  | PatNot(_, p) -> normpat_complement (pat_to_normpat p)

let pat_example_gives_complete_pattern = ref false

let pat_example normpat =
  let wildpat = PatNamed(NoInfo, NameWildcard) in
  let rec npat_to_pat = function
    | NSPat (SPatInt i) -> PatInt(NoInfo, i)
    | NSPat (SPatChar c) -> PatChar(NoInfo, c)
    | NSPat (SPatBool b) -> PatBool(NoInfo, b)
    | NSPat (SPatCon (str, np)) -> PatCon(NoInfo, str, nosym, npat_to_pat np)
    | NPatRecord (r, neg) ->
       let pos = PatRecord(NoInfo, Record.map npat_to_pat r) in
       UstringSet.elements neg
       |> List.map (fun label -> PatRecord(NoInfo, Record.singleton label wildpat))
       |> (function
           | [] -> pos
           | x::xs ->
              let neg = PatNot(NoInfo, List.fold_left (fun a b -> PatOr(NoInfo, a, b)) x xs) in
              if Record.is_empty r then neg else PatAnd(NoInfo, pos, neg))
    | NPatSeqTot nps -> PatSeqTot(NoInfo, List.map npat_to_pat nps |> Mseq.of_list)
    | NPatSeqEdg (pre, post) ->
       PatSeqEdg(NoInfo,
                 List.map npat_to_pat pre |> Mseq.of_list,
                 NameWildcard,
                 List.map npat_to_pat post |> Mseq.of_list)
    | NPatNot (seqs, cons) ->
       let seqs = match seqs with
         | None -> [PatSeqEdg(NoInfo, Mseq.empty, NameWildcard, Mseq.empty)]
         | Some lens ->
            IntSet.elements lens
            |> List.map (fun len -> PatSeqTot(NoInfo, repeat len wildpat |> Mseq.of_list)) in
       let cons =
         ConSet.elements cons
         |> List.map (function
                | IntCon i -> PatInt(NoInfo, i)
                | CharCon c -> PatChar(NoInfo, c)
                | BoolCon b -> PatBool(NoInfo, b)
                | ConCon str -> PatCon(NoInfo, str, nosym, wildpat)
                | RecCon -> PatRecord(NoInfo, Record.empty)) in
       match seqs @ cons with
       | [] -> wildpat
       | p::ps -> PatNot(NoInfo, List.fold_left (fun a b -> PatOr(NoInfo, a, b)) p ps)
  in
  if !pat_example_gives_complete_pattern
  then match NPatSet.elements normpat with
       | [] -> PatNot(NoInfo, PatNamed(NoInfo, NameWildcard))
       | np::nps -> List.fold_left (fun a b -> PatOr(NoInfo, a, npat_to_pat b)) (npat_to_pat np) nps
  else match NPatSet.choose_opt normpat with
       | None -> PatNot(NoInfo, PatNamed(NoInfo, NameWildcard))
       | Some np -> npat_to_pat np

type order_query =
| Subset
| Superset
| Equal
| Disjoint
| Overlapping of pat * pat * pat (* examples of patterns in only left, in both, and in only right *)

(* Compare the specificity order of two patterns. If you want to compare two patterns p1 and p2,
 * pass the arguments (pat_to_normpat p1, normpat_complement (pat_to_normpat p1)) and
 * (pat_to_normpat p2, normpat_complement (pat_to_normpat p2)). *)
let order_query ((ap, an): normpat * normpat) ((bp, bn): normpat * normpat): order_query =
  let a_minus_b = normpat_intersect ap bn in
  let b_minus_a = normpat_intersect bp an in
  if NPatSet.is_empty a_minus_b && NPatSet.is_empty b_minus_a then Equal
  else if NPatSet.is_empty a_minus_b then Subset
  else if NPatSet.is_empty b_minus_a then Superset
  else
    let overlapping = normpat_intersect ap bp in
    if NPatSet.is_empty overlapping then Disjoint
    else Overlapping (pat_example a_minus_b, pat_example overlapping, pat_example b_minus_a)
