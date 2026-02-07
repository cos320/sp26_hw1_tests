open Simulator
open Util.Assert
open X86
open Asm
(* From gradedtests.ml *)
let program_test (p:prog) (ans:int64) () =
  let res = assemble p |> load |> run in
  if res <> ans
  then failwith (Printf.sprintf("Expected %Ld but got %Ld") ans res)
  else ()

let machine_test (s:string) (n: int) (m: mach) (f:mach -> bool) () =
  for _i=1 to n do step m done;
  if (f m) then () else failwith ("expected " ^ s)

let sbyte_list (a: sbyte array) (start: int) : sbyte list =
  Array.to_list (Array.sub a start 8)

(* Insert your tests here.  Each should take follow the same pattern as the
   "zkincaid" suite below.  In particular, make sure that your suite begins
   with a comment that identifies the group members that contributed the test.
   Make sure to also append your tests to the student_tests list at the bottom
   of this file. *)

(* Tests for Zachary Kincaid *)
let zkincaid =
  let sqrt n =
    [ gtext "main"
        [ Movq, [~$1; ~%Rax] ]
    ; text "loop"
        [ Movq, [~%Rax; ~%Rdi ]
        ; Imulq, [~%Rdi; ~%Rdi ]
        ; Cmpq,  [~$n; ~%Rdi]
        ; J Gt, [~$$"exit"]
        ; Addq, [~$1; ~%Rax]
        ; Jmp, [~$$"loop"] ]
    ; text "exit"
        [ Subq, [~$1; ~%Rax]
        ; Retq, [] ]
    ]
  in
  [ ("sqrt4", program_test (sqrt 4) 2L)
  ; ("sqrt8", program_test (sqrt 8) 2L)
  ; ("sqrt9", program_test (sqrt 9) 3L)
  ; ("sqrt10", program_test (sqrt 10) 3L) ]

(* Tests for Raheem Idowu *)
let satsuma = 
  let gcd a b =
    [ gtext "main"
      [ Movq, [~$a; ~%Rax ]
      ; Movq, [~$b; ~%Rdi ] ]
    ; text "gcd"
      [ Cmpq, [~$0; ~%Rdi]
      ; J Eq, [~$$"return"]
      ; Cmpq, [~%Rdi; ~%Rax]
      ; J Ge, [~$$"noswitch"]
      ; Movq, [~%Rax; ~%Rdx]
      ; Movq, [~%Rdi; ~%Rax]
      ; Movq, [~%Rdx; ~%Rdi] ]
    ; text "noswitch"
      [ Subq, [~%Rdi; ~%Rax]
      ; Movq, [~%Rax; ~%Rdx]
      ; Movq, [~%Rdi; ~%Rax]
      ; Movq, [~%Rdx; ~%Rdi] 
      ; Jmp, [~$$"gcd"] ]
    ; text "return"
      [Retq, []]
    ]
  in
  [ ("gcd1_4", program_test (gcd 1 4) 1L)
  ; ("sqrt6_8", program_test (gcd 6 8) 2L)
  ; ("sqrt9_5", program_test (gcd 9 5) 1L)
  ; ("sqrt69_67", program_test (gcd 69 67) 1L)
  ; ("sqrt100_60", program_test (gcd 100 60) 20L) ]

let student_tests =
  []
  @ zkincaid (* Append your tests to this list *)
  @ satsuma

