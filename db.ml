(* 
	Compile instruction :
	-$ ocamlc cb.mli
	-$ ocamlopt -c db.ml
*)

(* type defined in mli file : *)
(*---------------------------*)
(* type of our elements, to identify null values *)
type 'a value =
  | Value of 'a
  | Null
;;

(* type defined in interface *)
type column_name = string
;;
type schema = column_name list
;;

type constraint_type =
  | Unique of column_name list
  | Not_null of column_name
;;
(*------------------------*)
(*
	@ requires
	@ ensures
	@ raises
*)
(* print a string contained in a Value *)
let printStr i = match i with
	| None -> ()
	| Some x -> match x with
		| Null -> ()
		| Value (n) -> print_string n
;;
(*
	@ requires i be Some Value int
	@ ensures print the data
	@ raises 
*)
(* print an int contained in a Value *)
let printInt i = match i with
	| None -> ()
	| Some x -> match x with
		| Null -> ()
		| Value (n) -> print_int n
;;


(* type for lines witc h is a collection of line *)
type lines = string list
;;

 (* type of our table  it contains the description (schema), the data itsself in lines and constraint with constraint_type *)
type table = { s : schema; l : lines; c : constraint_type}
;;

(* Use of trie structure to represent each line, for each line of one table a trie is created *)
(* Use of module Map to easily create our trie *)
module CMap = Map.Make(Char)
;;

(* our trie contains data using option type to easily reuse it 
In this project  we'll put char in each node (because our column name are string) *)
type 'a trie = Trie of ('a option * 'a trie CMap.t)
;;

(* an empty tree is a trie with no cata pointing to an empty Map *)
let emptyTrie = Trie (None, CMap.empty);;

(* addToLine allow to add an element in our trie in the node coresponding to the last char of str *)
(* 	@requires str might be empty but not null, the trie must exist but might be emptyTrie, ele
	@ensures that the element to be added (ele) is in the right place inside the trie given
	@raises nothing for now, should warn in the futur if add an element has erased another one 
*)
let rec addToLine str ele (Trie (value,tList)) = let len = ((String.length str) - 1) in match len with
	| 0 -> Trie (Some (Value ele), tList)
	| _ -> let child = try ( CMap.find (String.get str 0) tList )
		with
			| Not_found -> emptyTrie
		in Trie ( value, (CMap.add (String.get str 0) (addToLine (String.sub str 1 len) ele child) tList))
;;
(*
	@ requires a trie containing a valid map
	@ ensures to return the value at str inside the trie if it exist ( the value or str in the trie)
	@ raises nothing now, should warn if str not in trie
*)
let rec findInLine str (Trie (value,tList) as cur) = let len = ((String.length str) - 1) in match len with 
	| 0 -> cur
	| _ -> let child = try ( CMap.find (String.get str 0) tList )
		with
			| Not_found -> emptyTrie
		in findInLine (String.sub str 1 len) child
;;
(*
	@ requires a trie that is not null but might be emptyTrie
	@ ensures to return the value in the trie
	@ raises
*)

(* test of addToLine and findInLine function *)
let getValue (Trie (value,tList)) = value;;

let test = addToLine "toto" "test" emptyTrie;;

printStr (getValue (findInLine "toto" test))


(* todo : complete *)
let verifyConstraint tbl name ele cstr_type = match cstr_type with
	| Unique l -> true
	| Not_null c -> true
;;

