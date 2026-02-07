open Simulator
open Util.Assert
open X86
open Asm

(* From gradedtests.ml *)
let program_test (p : prog) (ans : int64) () =
  let res = assemble p |> load |> run in
  if res <> ans then
    failwith (Printf.sprintf "Expected %Ld but got %Ld" ans res)
  else ()

let machine_test (s : string) (n : int) (m : mach) (f : mach -> bool) () =
  for _i = 1 to n do
    step m
  done;
  if f m then () else failwith ("expected " ^ s)

(* Run a program, then evaluate the state of the machine using the 
   given function. *)
let program_test_adv (s : string) (p : prog) (f : mach -> bool) () =
  let m = assemble p |> load in
  let _ = run m in
  if f m then () else failwith ("expected " ^ s)

(* Check if the values in registers R08 to R13 exclusive are in sorted order. *)
let check_sorted_list (m : mach) : (bool) = 
  (* Output list stored in registers R08 to R13 inclusive *)
  if (get_quad_from_reg m R08) > (get_quad_from_reg m R09) then false
  else if (get_quad_from_reg m R09) > (get_quad_from_reg m R10) then false
  else if (get_quad_from_reg m R10) > (get_quad_from_reg m R11) then false
  else if (get_quad_from_reg m R11) > (get_quad_from_reg m R12) then false
  else if (get_quad_from_reg m R12) > (get_quad_from_reg m R13) then false
  else true

let sbyte_list (a : sbyte array) (start : int) : sbyte list =
  Array.to_list (Array.sub a start 8)

(* Insert your tests here.  Each should take follow the same pattern as the
   "zkincaid" suite below.  In particular, make sure that your suite begins
   with a comment that identifies the group members that contributed the test.
   Make sure to also append your tests to the student_tests list at the bottom
   of this file. *)

(* Tests for Zachary Kincaid *)
let zkincaid =
  let sqrt n =
    [
      gtext "main" [ (Movq, [ ~$1; ~%Rax ]) ];
      text "loop"
        [
          (Movq, [ ~%Rax; ~%Rdi ]);
          (Imulq, [ ~%Rdi; ~%Rdi ]);
          (Cmpq, [ ~$n; ~%Rdi ]);
          (J Gt, [ ~$$"exit" ]);
          (Addq, [ ~$1; ~%Rax ]);
          (Jmp, [ ~$$"loop" ]);
        ];
      text "exit" [ (Subq, [ ~$1; ~%Rax ]); (Retq, []) ];
    ]
  in
  [
    ("sqrt4", program_test (sqrt 4) 2L);
    ("sqrt8", program_test (sqrt 8) 2L);
    ("sqrt9", program_test (sqrt 9) 3L);
    ("sqrt10", program_test (sqrt 10) 3L);
  ]

(* Tests for Arnav Ambre *)
let arnav =
  let insertion_sort a1 a2 a3 a4 a5 a6 =
    [
      gtext "main" 
        [ (* Load parameters into the array in the data segment. *)
          (Leaq, [ Ind1 (Lbl "array"); ~%Rdx ]);
          (Movq, [ ~$a1; Ind2 (Rdx) ]);
          (Addq, [ ~$8; ~%Rdx ]);
          
          (Movq, [ ~$a2; Ind2 (Rdx) ]);
          (Addq, [ ~$8; ~%Rdx ]);
          
          (Movq, [ ~$a3; Ind2 (Rdx) ]);
          (Addq, [ ~$8; ~%Rdx ]);
          
          (Movq, [ ~$a4; Ind2 (Rdx) ]);
          (Addq, [ ~$8; ~%Rdx ]);
          
          (Movq, [ ~$a5; Ind2 (Rdx) ]);
          (Addq, [ ~$8; ~%Rdx ]);
          
          (Movq, [ ~$a6; Ind2 (Rdx) ]);
          (Leaq, [ Ind1 (Lbl "array"); ~%Rax ]); 
          (Leaq, [ Ind1 (Lbl "array"); ~%Rcx ]);
        ];
      text "outer_loop"
        [
          (* %rax is i, pointer to current element, 
             %rbx is j, pointer to previous element(s) being evaluated, 
             %rcx is pointer to first element of array, 
             %rdx is pointer to last element of array, 
             %rsi is value of current element *)
          (Cmpq, [~%Rdx ; ~%Rax]); (* Check if we're done sorting the list. *)
          (J Gt, [ ~$$"exit" ]);

          (* Get value of the current element at i. *)
          (Movq, [ Ind2 (Rax); ~%Rsi ]);

          (Movq, [ ~%Rax; ~%Rbx]);
          (Subq, [ ~$8; ~%Rbx]); (* Move j to the previous element. *)
        ];
      text "inner_loop"
        [
          (* Check if j reached the beginning of the list. *)
          (Cmpq, [~%Rcx ; ~%Rbx]); 
          (J Lt, [ ~$$"end_inner_loop" ]);

          (* Check if the current element is greater than the previous element 
            pointed to by j, as desired (for sorting in increasing order). *)
          (Cmpq, [Ind2 (Rbx) ; ~%Rsi]);
          (J Ge, [ ~$$"end_inner_loop" ]);

          (* If not, we swap the element at j with the current element. *)
          (Movq, [ Ind2 (Rbx); ~%Rdi ]);
          (Addq, [ ~$8; ~%Rbx]);
          (Movq, [ ~%Rdi; Ind2 (Rbx) ]);

          (* Move j back down again to the previous element. *)
          (Subq, [ ~$16; ~%Rbx]);
          (Jmp, [ ~$$"inner_loop" ])
        ];
      text "end_inner_loop"
        [
          (* Store the current element after the value point to by j. *)
          (Addq, [ ~$8; ~%Rbx]); 
          (Movq, [ ~%Rsi; Ind2 (Rbx) ]);
          
          (Addq, [ ~$8; ~%Rax]); (* Move i up to access next element. *)
          (Jmp, [ ~$$"outer_loop" ])
        ];
      text "exit" 
        [ (* Move sorted array to registers R08 - R13 inclusive to allow for 
             inspection by test program. *)
          (Movq, [ Ind2 (Rcx); ~%R08 ]);
          (Addq, [ ~$8; ~%Rcx ]);
          
          (Movq, [ Ind2 (Rcx); ~%R09 ]);
          (Addq, [ ~$8; ~%Rcx ]);
          
          (Movq, [ Ind2 (Rcx); ~%R10 ]);
          (Addq, [ ~$8; ~%Rcx ]);
          
          (Movq, [ Ind2 (Rcx); ~%R11 ]);
          (Addq, [ ~$8; ~%Rcx ]);
          
          (Movq, [ Ind2 (Rcx); ~%R12 ]);
          (Addq, [ ~$8; ~%Rcx ]);
          
          (Movq, [ Ind2 (Rcx); ~%R13 ]);
          (Retq, []) 
        ];
      data "array" 
        [ (* Placeholder for array to be sorted. *)
          Quad (Lit 0L); Quad (Lit 0L); Quad (Lit 0L); 
          Quad (Lit 0L); Quad (Lit 0L); Quad (Lit 0L);
        ];
    ]
  in
  [
    ("ins_sort_already_sorted", program_test_adv "sorted list" 
      (insertion_sort 1 2 3 4 5 6) check_sorted_list);
    ("ins_sort_reverse_sorted", program_test_adv "sorted list" 
      (insertion_sort 6 5 4 3 2 1) check_sorted_list);
    ("ins_sort_all_equal", program_test_adv "sorted list" 
      (insertion_sort 1 1 1 1 1 1) check_sorted_list);
    ("ins_sort_negative_values", program_test_adv "sorted list" 
      (insertion_sort (-6) (-3) (-9) (-4) (-1) (-7)) check_sorted_list);
    ("ins_sort_pos_neg_values", program_test_adv "sorted list" 
      (insertion_sort (-1) (2) (0) (-4) (23) (-9)) check_sorted_list);
  ]

let student_tests = 
  [] 
  @ zkincaid (* Append your tests to this list *)
  @ arnav 
