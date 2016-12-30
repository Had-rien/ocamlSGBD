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

(* Use of trie structure to represent each line, for each line of one table a trie is created *)
(* Use of module Map to easily create our trie *)
module CMap = Map.Make(Char)
;;

(* our trie contains data using option type to easily reuse it 
In this project  we'll put char in each node (because our column name are string) *)
type 'a trie = Trie of ('a value * 'a trie CMap.t)
;;

(* an empty tree is a trie with no cata pointing to an empty Map *)
let emptyTrie = Trie (Null, CMap.empty);;

(* addToLine allow to add an element in our trie in the node coresponding to the last char of str *)
(* 	@requires str might be empty but not null, the trie must exist but might be emptyTrie, ele
	@ensures that the element to be added (ele) is in the right place inside the trie given
	@raises nothing for now, should warn in the futur if add an element has erased another one 
*)
let rec addToLine str ele (Trie (value,tList)) = let len = ((String.length str) - 0) in match len with
	| 0 -> Trie ( ele, tList) (* end of str, we put ele inside the node *)
	| _ -> let child = try ( CMap.find (String.get str 0) tList ) (* test if first char of str is in the map of this node *)
		with
			| Not_found -> emptyTrie (* if not we create a new node *)
		(* eather way we create a new tree replacing the one in argument with the right parametersne
		*)
		in Trie ( value, (CMap.add (String.get str 0) (addToLine (String.sub str 1 (len-1)) ele child) tList))
;;

(*
	@ requires a trie that is not null but might be emptyTrie
	@ ensures to return the value in the trie
	@ raises
*)
let getValue (Trie (value,tList)) = value;;

(*
	@ requires a trie containing a valid map
	@ ensures to return the value at str inside the trie if it exist ( the value or str in the trie)
	@ raises nothing now, should warn if str not in trie
*)
let rec findInLine str (Trie (value,tList) as cur) = let len = ((String.length str) - 1) in match len with 
	| 0 -> getValue cur
	| _ -> let child = try ( CMap.find (String.get str 0) tList )
		with
			| Not_found -> emptyTrie
		in findInLine (String.sub str 1 len) child
;;

(*
	@ requires a trie that is not null but might be emptyTrie
	@ ensures to print a representation of the trie, not pretty but allow to understand the representation
	@ raises
*)
let rec printTrie c (Trie (value,tList)) = 
	print_string "["; print_char c; print_string ", ";
	match tList = CMap.empty with
		| true -> printStr value; print_string "]";  print_newline ();
		| _ -> printStr value; print_string "]"; (CMap.iter printTrie tList);
;;

(*
	@ requires a trie that is not null but might be emptyTrie, f is a function that takes a Value and return one
	@ ensures to apply f to all values of the given trie and return it
	@ raises
*)
let rec tmap f (Trie (value,tList)) = 
	match tList = CMap.empty with
		| true -> Trie ((f value), tList)
		| _ -> Trie ((f value), (CMap.map (tmap f) tList))
;;

(*
	@ requires a trie that is not null but might be emptyTrie, f is a function that takes 2 Value and return one
	@ ensures to apply f to all values recursivly 
	@ raises
*)(*
let rec fold_line fon acc (Trie (value,tList) as trie) = (CMap.fold fon acc tList )
;;
*)
(* 
 	@requires str might be empty but not null, the trie must exist but might be emptyTrie, ele
	@ ensures to call addToLine only if we insert a not empty string
	@ raises
*)
let checkAddTrie str ele trie = match ele with
	| "" -> trie
	| _ -> addToLine str (Value ele) trie
;;

(*----------end of line representation functions ------*)

(* type for lines witch is a collection of line *)
type 'a lines = ('a value) trie
;;

 (* type of our table  it contains the description (schema), the data itsself in lines and constraint with constraint_type *)
type 'a table = { s : schema; l : ('a value) lines; c : constraint_type}
;;

let rec getClef line columnList = match columnList with
	| [] -> ""
	| c1::[] -> if (String.get c1 0) = 'c' then c1 else ""
	| c1::l -> match (String.get c1 0) with
			| 'c' -> (match (findInLine c1 line) with 
				| Value (n) ->  n
				| Null -> "" )
			| _ -> getClef line l
;;

let addLine newL (s, l, c) =  (s, (addToLine (getClef newL s ) (Value newL) l), c)
;;

(*----------TEST----------------*)
(* test of addToLine and findInLine function *)

let test = checkAddTrie "teto" "test" emptyTrie;;

let test = checkAddTrie "ctata" "yep" test;;

let test = checkAddTrie "tooo" "non" test;;

let test = checkAddTrie "null" "" test;;


printStr ((findInLine "toto" test));;
print_newline ();;
printTrie ' ' test;;

(* test of tmap, exemple of a function needed for tmap  *)
let uppercaseValue value = match value with
	| Null -> Null
	| Value a -> Value ((String.uppercase_ascii a))
;;

printTrie ' ' (tmap uppercaseValue test);;

(* test of fold_line, exemple of a function needed for fold_line : (key -> 'a -> 'b -> 'b) *)
let concatLine car value acc = match value with
	| Null -> acc
	| Value a -> (String.concat "; " (acc::a::[]))
;;
(*
print_string (fold_line concatLine "ligne" test);;
*)
let schemaTest = "teto"::"ctata"::"tooo"::[]
;;

let testTable = (schemaTest, emptyTrie, "notnull")
;;

let testTable = addLine test testTable
;;

let testTable = addLine test testTable
;;

(* marche pas puisque le trie de line ne stocke pas de string value mais des line value *)
let printTable (s, l, c) = printTrie ' ' l
;;


(* todo : complete *)
let verifyConstraint tbl name ele cstr_type = match cstr_type with
	| Unique l -> true
	| Not_null c -> true
;;

