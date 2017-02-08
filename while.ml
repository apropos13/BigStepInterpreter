(* 
README: 
This project was compiled using an OCaml interpreter 
with version 4.02.1 on a x86_64 bit machine

To compile type and suppress warnings: ocaml -w a while.ml 

Assignment #2
Program: while.ml
Authors: Panos Karagiannis (ID: 1309484)

The logic of the program is implemented in eval function
*)




(*In implementing an interpeter for the WHILE language some assumptions were made:

a. An enviroment (state) variable has to exist that contains all valid variables in the language.
   The enviroment variable need not always be supplied to the eval function, unless the epxression
   contains a variable of type `Var (see below definition of a_exp)

b. The semantic function "eval" is defined as follows, Eval:(a_exp * b_exp * command) -> (State -> return_type)
   Where the state function is defined as State: `Var-> `RetInt. The definition of return_type is found below  *)

(* Program explanation in comments ...*)


(*Notice that we need to define the different kinds of expressions as polymorphic variant data types,
otherwise we would have problems in defining the functions that take
as argument a general exprerssion*)
type a_exp= 
  [ `Int of int
  |`Var of string 
  |`SumArExp of a_exp * a_exp
  | `SubtrArExp of a_exp * a_exp
  | `MulArExp of a_exp * a_exp
  | `DivArExp of a_exp * a_exp];; (*<------ Extra feature: Integer Division*)
  
			  

type b_exp=
  [ `Bool of bool
  |`Equal of a_exp * a_exp
  |`Less of a_exp * a_exp
  |`Not of b_exp
  |`And of b_exp * b_exp
  |`Or of b_exp * b_exp];;


type command= 
[ `Skip
| `Assign of string * a_exp
| `Sequence of command * command
| `If_Then_Else of b_exp * command * command
| `While_Do of b_exp * command]
;;

(*The types that our language While return*)
(* Need to unify them under one datatype to 
be able to create a function that returns them all*)
type return_type=
  [`RetInt of int (*Aexp return this*)
  |`RetBool of bool (*Bexp return this*)
  | `RetNothing of unit] (*Commands return this*)
;;

(*Define the accepted elements of the enviroment *)
type var_pairs  = Name of string 
               | Value  of a_exp ref ;;

		       
(*Helper function for Aexp manipulations *)  
let plus (x,y) = match (x,y) with
  | (`RetInt(w),`RetInt(z))->`RetInt(w+z)
  |_->failwith ("type error in plus");;

(*Helper function for Aexp manipulations *)
let minus (x,y) =match (x,y) with
  | (`RetInt(w), `RetInt(z))->`RetInt(w-z)
  |_-> failwith ("type error in minus");;

(*Helper function for Aexp manipulations *)
let times (x,y)= match (x,y) with
  | (`RetInt(w), `RetInt(z))->`RetInt(w*z)
  |_->failwith ("type error in times");;

(*Helper function for Aexp manipulations *)
let div (x,y)= match (x,y) with
  | (`RetInt(w), `RetInt(0))-> failwith ("Error: Division by Zero")
  | (`RetInt(w), `RetInt(z))->`RetInt(w/z)
  |_->failwith ("type error in div");;

  
(*Helper function for Aexp manipulations. This function searches the 
enviroment and assigns a value to the variable var *)
let rec get_env_value env var = match env with
  |[]-> failwith ("ERROR: Variable not propely initialized")
  |hd::tl -> (match hd with
	       |(Name a,Value b)->(match !b with
				   |(`Int v)-> if (var = a)
						  then`RetInt v
						  else get_env_value tl var
				   |_-> failwith ("ERROR: Variable not an integer")
			          )
	       |_->failwith("Invalid inputs") )
;;
  
 
(*Helper function, allows us to return to the `Int space from
`RetInt, if computation is still to be done*)   
let convert_ret_to_int c = match c with
  | `RetInt a -> `Int a
  | _->failwith ("Invalid input")


(*Used in the `Assign command. Assigns a new value to the variable
with name var. The enviroment variable is physically changed to allow 
program coherence among various commands *)
let rec add_reset_variable env var value = match env with
  |[]-> ( env@[  (Name var, Value (ref (value) ) ) ] ; () ) (*Add a new variable if it does not exist *)
  |hd::tl ->  (match hd with
	       |(Name a,Value b)->(match !b with
				   |(`Int v)-> if (var = a)
						  then  b:= value
						  else add_reset_variable tl var value
				   |_->  failwith ("ERROR: Variable cannot be bool")
			          )
	       |_->failwith("Invalid arguments") )
;;

(*Helper function for Bexp*)
  let negate b =match b with
    |`Bool(b_in)->`RetBool(not b_in)
    |`RetBool(b_in)-> `RetBool(not b_in)
    |_-> failwith ("type error in negate");;
    
(*Helper function for Bexp*)
  let is_equal(x,y) = match (x,y) with
    |(`RetInt(w),`RetInt(z))-> if w==z then `RetBool(true) else `RetBool(false)
    |_->failwith ("type error in equal");;
		 
(*Helper function for Bexp*)
  let is_less(x,y) = match (x,y) with
    |(`RetInt(w),`RetInt(z))-> if w<z then `RetBool(true) else `RetBool(false)
    |_->failwith ("type error in negate");;
		 
(*Helper function for Bexp*)
  let do_and(x,y) = match (x,y) with
    |(`RetBool(w),`RetBool(z))-> if w&&z then `RetBool(true) else `RetBool(false)
    |_->failwith ("type error in negate");;
		 
(*Helper function for Bexp*)
  let do_or(x,y) = match (x,y) with
    |(`RetBool(w),`RetBool(z))-> if w||z then `RetBool(true) else `RetBool(false)
    |_->failwith ("type error in negate");;
		 
					  
(*Helper function for Bexp, checks if a `Retbool expr is true or false *)
let is_true bool_exp = match bool_exp with
  | `RetBool(true) ->  true
  | `RetBool(false)->false 
  |_->failwith ("Not a RetBool. Incorrect types")
;;
  

(* The evaluator function, which is the core of the interpreter*)
let rec eval ?env_name:(env=[])  exp = match exp with

    (*Arithmetic Expressions Cases --> Return `RetInt (<int>) *)
  |`RetInt e -> `RetInt e
  |`RetBool b -> `RetBool b
  |`RetNothing-> `RetNothing
  |`Int e ->`RetInt e
  | `Var v-> get_env_value env v 
  | `SumArExp(a1,a2)->plus( eval ~env_name:(env) (a1), eval ~env_name:(env) (a2) )
  | `SubtrArExp(a1,a2)->minus( eval ~env_name:(env) a1, eval ~env_name:(env) a2)
  | `MulArExp(a1,a2)->  times ( eval ~env_name:(env) (a1), eval ~env_name:(env) (a2) )
  | `DivArExp(a1,a2)->  div ( eval ~env_name:(env) (a1), eval ~env_name:(env) (a2) ) (*Extra Feature; Integer Division*)

  (* Boolean Expression cases--> Return `RetBool (<bool>) *)			      
  | `Bool b -> `RetBool b	   
  | `Not b -> negate ( eval ~env_name:(env) b)
  | `Equal(a1,a2) -> is_equal(  eval ~env_name:(env) (a1), eval ~env_name:(env) (a2) )
  | `Less(a1,a2) ->  is_less( eval ~env_name:(env) (a1), eval ~env_name:(env) (a2) )
  | `And (b1,b2) -> do_and( eval ~env_name:(env) (b1), eval ~env_name:(env) (b2) )
  | `Or (b1,b2)-> do_or( eval ~env_name:(env) (b1), eval ~env_name:(env) (b2) )


  (* Command cases --> Return unit () *)		       
  | `Assign(`Var avar,aval)->( add_reset_variable env avar (convert_ret_to_int (eval ~env_name:(env) aval) ) ; `RetNothing)
  |`While_Do(b,c)->( while (is_true (eval  ~env_name:(env) b ) ) do (eval  ~env_name:(env) c) done   ;  `RetNothing)		      
  |`Skip -> `RetNothing
  |`If_Then_Else(b,c1,c2)->( if is_true( eval ~env_name:(env)( b) )
			   then  eval ~env_name:(env) (c1)
			   else eval ~env_name:(env) (c2) ; `RetNothing )
										   
  |`Sequence(c1,c2)-> eval  ~env_name:(env) ( c1) ; eval  ~env_name:(env)( c2) ; `RetNothing
  |_->failwith ("Invalid expr")			      
;;

(*---------TEST CASES-----------*)

(*Initialize the enviroment *)
let enviroment= [ (Name "x", Value (ref (`Int 5) ) ); (Name "y", Value (ref (`Int 1))) ; (Name "p", Value ( ref (`Int (2))));  (Name "q", Value ( ref (`Int (10))))  ];;

let test_add_reset= add_reset_variable  enviroment "p" (`Int 10)   ;;
  
assert (eval  ~env_name:(enviroment) (`Equal( `Var "p", `Int 10)) = `RetBool true) ;;

let test_add_reset= add_reset_variable enviroment "p" (`Int (-10) );;

  
let gv =get_env_value enviroment "x";;
  
let test_is_true = is_true (`RetBool true);;

let s=`SumArExp(`Int 2,`Int 3);;
let subtr= `SubtrArExp(`Int 9, `Int 8);;
let mult = `MulArExp( `Int 8, `Int 5);;

  assert (eval mult = `RetInt 40);;
  assert(eval subtr = `RetInt 1);;
  assert(eval s = `RetInt 5);;

let integer_eval= `Int 115  ;;
assert (eval integer_eval = `RetInt 115) ;; (*Notice how the parameter enviroment is not neccessairy, since no variable is present*)

(* 5==5*)
let equality =  (`Equal(`Int 5, `Int 5));;
 assert( eval equality= `RetBool true) ;;
  
(* (10-5) == (3+2) *)
let equality_Aexp = (`Equal (`SubtrArExp(`Int 10, `Int 5)  , `SumArExp(`Int 3, `Int 2)));;
assert ( eval equality_Aexp = ` RetBool true) ;;

(* 10/5 == 0+2 *)
let equality_Aexp = (`Equal (`DivArExp(`Int 10, `Int 5)  , `SumArExp(`Int 0, `Int 2)));;
assert ( eval equality_Aexp = ` RetBool true) ;;

  (* 5== 3+2*)
let t4=eval (`Equal ( `Int 5  , `SumArExp(`Int 3, `Int 2)));;
 assert( t4=`RetBool true);;
	      
(* x-1==3 (the value of x is taken from the enviroment, and it is 5 hance this is false) *)  
assert ( eval  ~env_name:(enviroment) (`Equal (`SubtrArExp( (`Var "x") , `Int 1) , `RetInt 2) )= `RetBool false);;

(* if t4 then x=15 ; x-1 else y=1 *)
let t6 = eval ~env_name:(enviroment) (`If_Then_Else
				       ( t4 ,`Sequence
					    (`Assign(`Var "x", `Int 15),`SubtrArExp( (`Var "x") , `Int 1))  ,
					 `Assign( `Var "y",`Int 1) ));;
  

assert ( eval ~env_name:(enviroment) (`Var "x") = `RetInt 15) ;;


  (*x=99+2; x-1 *)      
let t7 = eval  ~env_name:(enviroment) (`Sequence(
					  (`Assign(`Var "x",  `SumArExp(`Int 99, `Int 2) )),
					 `Assign ( `Var "x", `SubtrArExp( (`Var "x") , `Int 1) ) ) );;

  
assert ( eval ~env_name:(enviroment) (`Var "x") = `RetInt 100) ;;

(*l = 8 *)
let assign_new_variable = `Assign(`Var "l", `Int 8);;
assert ( eval  ~env_name:(enviroment) ( assign_new_variable ) = `RetNothing )
			   
(* while y<10 do y=y+1 , at this point y=1*)
let while_command = ( `While_Do( `Less(`Var "y" , `Int 10 ) , `Assign(`Var "y" , `SumArExp(`Var "y"  , `Int 1) )    )    );;
let t8= eval ~env_name:(enviroment) while_command ;;
  (* hence y now should be `RetInt 10*)
 assert ( eval ~env_name:(enviroment) (`Var "y") = `RetInt 10) ;;

   

   (* Not ( x == y) <==> Not ( 100 == 10 ) <==> Not ( false )=true *)
 let negate_bool = `Not ( `Equal ( `Var "x", `Var "y") )   ;;
   assert ( eval ~env_name:(enviroment)  (negate_bool)= `RetBool true) ;;


(* while p<100 do x=2*x ; p= p - (-2) done *)
(* since p= -10, x=101 and at every iteration we do p=p+2 we iterate p+2n<101 <==> n<111/2=55.5 times
this means that x becomes : x= 2^55 * 100 = 3602879701896396800 *)
       
   let long_while = `While_Do
		     ( `Less(`Var "p", `Int 100) ,
		       `Sequence
			( `Assign(`Var "x" ,
				  `MulArExp(`Var "x", `Int 2) ),
			  `Assign(`Var "p" ,
				  `SubtrArExp(`Var "p", `Int (-2)) ) )) ;;

eval ~env_name:(enviroment) long_while;;
assert ( eval ~env_name:(enviroment) (`Var "x") = `RetInt 3602879701896396800) ;;
assert ( eval ~env_name:(enviroment) (`Var "p") = `RetInt 100) ;;

(* SKip ; p=9 *)
let skip_test= `Sequence ( `Skip ,
			   `Assign ( `Var "p", `RetInt (-9) )  ) ;;

  eval ~env_name:(enviroment) skip_test;;
  assert ( eval ~env_name:(enviroment) (`Var "p") = `RetInt (-9) ) ;;
