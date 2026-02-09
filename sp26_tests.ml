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

(* Check if the values in registers R08 to R13 inclusive are in sorted order. *)
let check_sorted_list (m : mach) : (bool) = 
  if m.regs.(rind R08) > m.regs.(rind R09) then false
  else if m.regs.(rind R09) > m.regs.(rind R10) then false
  else if m.regs.(rind R10) > m.regs.(rind R11) then false
  else if m.regs.(rind R11) > m.regs.(rind R12) then false
  else if m.regs.(rind R12) > m.regs.(rind R13) then false
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


(* Tests for Richard and John *)
let richard_john = 
    
  let bin_search (target:int) (lst_len:int) (lst:int list) = 
    [ gtext "main"
      [ 
        (* R08 - lo, R09 - hi, R10 - mid, Rax starts of -1*)
        (Movq, [~$0; ~%R08]);
        (Movq, [~$(lst_len - 1); ~%R09]);
        (Movq, [~$0; ~%R10]);
        (Movq, [~$(-1); ~%Rax]);
        (Jmp, [~$$"bsearch"])

      ]
      ; text "bsearch"
      [
        (* if lo > hi return -1*)
        (Cmpq, [~%R09; ~%R08]);
        (J Gt, [~$$"exit"]);

        (* mid = (lo + hi) >>> 1 *)
        (Movq, [~%R08; ~%R10]);
        (Addq, [~%R09; ~%R10]);
        (Sarq, [~$1; ~%R10]);

        (* load arr[mid] into Rsi, 
        use R11 as a temp calculation register *)
        (Leaq, [Ind1 (Lbl "array"); ~%Rsi]);
        (Movq, [~%R10; ~%R11]);
        (Imulq, [~$8; ~%R11]);
        (Addq, [~%R11; ~%Rsi]);
        (Movq, [Ind2 (Rsi); ~%Rsi]);

        (* if target > arr[mid], lo = mid + 1 *)
        (Cmpq, [~%Rsi; ~$target]);
        (J Gt, [~$$"target_gt_mid"]);

        (* if target < arr[mid], hi = mid + 1 *)
        (J Lt, [~$$"target_lt_mid"]);

        (* fallthrough target = arr[mid] case, rax = mid, return *)
        (Movq, [~%R10; ~%Rax]);
        (Jmp, [~$$"exit"])
        
      ]
      ; text "target_gt_mid"
      [
        (* lo = mid + 1 *)
        (Movq, [~%R10; ~%R08]);
        (Addq, [~$1; ~%R08]);
        (Jmp, [~$$"bsearch"])
      ]
      ; text "target_lt_mid"
      [
        (* hi = mid - 1 *)
        (Movq, [~%R10; ~%R09]);
        (Subq, [~$1; ~%R09]);
        (Jmp, [~$$"bsearch"]);
      ]
      ; text "exit"
      [
        (Retq, [])
      ]
      ; data "array" (List.map (fun x -> Quad (Lit (Int64.of_int x))) lst)

    ] 
  in
  [
    ("bin_search1", program_test (bin_search 0 1 [0]) 0L);
    ("bin_search2", program_test (bin_search 16 10 (List.init 10 (fun x -> x*x)) ) 4L);
    ("bin_search3", program_test (bin_search 123 1000 (List.init 1000 (fun x -> x)) ) 123L);
    ("bin_search4", program_test (bin_search 123 1000 (List.init 1000 (fun x -> (x-500) )) ) (623L));
    ("bin_search5", program_test (bin_search 1500 1000 (List.init 1000 (fun x -> x)) ) (-1L));
    ("bin_search6", program_test (bin_search 1797 1000 (List.init 1000 (fun x -> 2*x)) ) (-1L));
  ]


(* Tests for Ben Aepli and Vedant Badoni ('compilers' group) *)
let aepli_badoni = 
  let uf n = 
    let n = max n 4 in
    [ text "uf_init" [
        Movq, [~$0; ~%Rcx];
        Movq, [~%Rsi; ~%Rax];

        Movq, [~%Rsi; ~%R08];
        Movq, [~%Rsi; ~%R09];
        Movq, [~%Rdi; ~%R10];
        Imulq, [~$8; ~%R10];
        Addq, [~%R10; ~%R09];

        Movq, [~%R09; ~%Rdx]
      ];
      text "uf_init_loop" [
        Cmpq, [~%Rdi; ~%Rcx];
        J Ge, [~$$"uf_init_endloop"];
        Movq, [~%Rcx; Ind2 R08];
        Movq, [~$1; Ind2 R09];
        Incq, [~%Rcx];
        Movq, [~$8; ~%R10];
        Addq, [~%R10; ~%R08];
        Addq, [~%R10; ~%R09];
        Jmp, [~$$"uf_init_loop"];
      ];
      text "uf_init_endloop" [
        Retq, []
      ];

      text "uf_find" [
        Movq, [~%Rdi; ~%Rax];
      ];
      text "uf_find_loop" [
        Movq, [~%Rax; ~%Rdi];
        Imulq, [~$8; ~%Rdi];
        Movq, [~%Rsi; ~%R08];
        Addq, [~%Rdi; ~%R08];
        Movq, [Ind2 R08; ~%R09];
        Cmpq, [~%Rax; ~%R09];
        J Eq, [~$$"uf_find_endloop"];
        Movq, [~%R09; ~%Rax];
        Jmp, [~$$"uf_find_loop"];
      ];
      text "uf_find_endloop" [
        Retq, []
      ];

      text "uf_connected" [
        Pushq, [~%Rsi];
        Pushq, [~%Rdx];
        Movq, [~%Rdx; ~%Rsi];
        Callq, [~$$"uf_find"];
        Popq, [~%Rsi];
        Popq, [~%Rdi];
        Pushq, [~%Rax];
        Callq, [~$$"uf_find"];
        Popq, [~%R08];
        Movq, [~%Rax; ~%R09];
        Movq, [~$0; ~%Rax];
        Cmpq, [~%R08; ~%R09];
        Set Eq, [~%Rax];
        Retq, [];
      ];

      text "uf_union" [
        Pushq, [~%Rbp];
        Movq, [~%Rsp; ~%Rbp];
        Pushq, [~%Rdi];
        Pushq, [~%Rsi];
        Pushq, [~%Rdx];
        Pushq, [~%Rcx];
        Movq, [~%Rdx; ~%Rsi];
        Callq, [~$$"uf_find"];
        Movq, [Ind3 (Lit (-16L), Rbp); ~%Rdi];
        Movq, [Ind3 (Lit (-24L), Rbp); ~%Rsi];
        Pushq, [~%Rax];
        Callq, [~$$"uf_find"];
        Popq, [~%Rcx];
        Cmpq, [~%Rcx; ~%Rax];
        J Eq, [~$$"uf_union_end"];
        Movq, [~%Rcx; ~%R10];
        Movq, [~%Rax; ~%R11];
        Imulq, [~$8; ~%R10];
        Imulq, [~$8; ~%R11];
        Movq, [ Ind3 (Lit (-32L), Rbp); ~%Rdi];
        Movq, [~%Rdi; ~%Rsi];
        Addq, [~%R10; ~%Rdi];
        Addq, [~%R11; ~%Rsi];
        Movq, [Ind2 Rdi; ~%R08];
        Movq, [Ind2 Rsi; ~%R09];
        Cmpq, [~%R08; ~%R09];
        J Ge, [~$$"uf_union_elsebranch"];
      ];
      text "uf_union_ifbranch" [
        Movq, [Ind3 (Lit (-24L), Rbp); ~%Rcx];
        Addq, [~%R10; ~%Rcx];
        Movq, [~%Rax; Ind2 Rcx];
        Addq, [~%R08; Ind2 Rsi];
        Jmp, [~$$"uf_union_end"];
      ];
      text "uf_union_elsebranch" [
        Movq, [Ind3 (Lit (-24L), Rbp); ~%Rax];
        Addq, [~%R11; ~%Rax];
        Movq, [~%Rcx; Ind2 Rax];
        Addq, [~%R09; Ind2 Rdi];
      ];
      text "uf_union_end" [
        Movq, [~%Rbp; ~%Rsp];
        Movq, [Ind2 Rbp; ~%Rbp];
        Addq, [~$8; ~%Rsp];
        Retq, [];
      ];

      gtext "main" [
        Pushq, [~%Rbp];
        Movq, [~%Rsp; ~%Rbp];
        Movq, [~$n; ~%Rdi];
        Movq, [~$0x408000; ~%Rsi];
        Pushq, [~%Rdi];
        Callq, [~$$"uf_init"];
        Pushq, [~%Rax];
        Pushq, [~%Rdx];
        Movq, [~$0; ~%Rdi];
        Movq, [~$3; ~%Rsi];
        Movq, [~%Rdx; ~%Rcx];
        Movq, [~%Rax; ~%Rdx];
        Callq, [~$$"uf_union"];
        Movq, [~$1; ~%Rdi];
        Movq, [~$3; ~%Rsi];
        Movq, [Ind3 (Lit (-16L), Rbp); ~%Rdx];
        Movq, [Ind3 (Lit (-24L), Rbp); ~%Rcx];
        Callq, [~$$"uf_union"];
        Movq, [~$2; ~%Rdi];
        Movq, [~$0; ~%Rsi];
        Movq, [Ind3 (Lit (-16L), Rbp); ~%Rdx];
        Movq, [Ind3 (Lit (-24L), Rbp); ~%Rcx];
        Callq, [~$$"uf_union"];
        Movq, [~$1; ~%Rdi];
        Movq, [~$2; ~%Rsi];
        Movq, [Ind3 (Lit (-16L), Rbp); ~%Rdx];
        Callq, [~$$"uf_connected"];
        Cmpq, [~$0; ~%Rax];
        J Eq, [~$$"main_failure"];
        Movq, [~$0; ~%Rdi];
        Movq, [Ind3 (Lit (-8L), Rbp); ~%Rsi];
        Subq, [~$1; ~%Rsi];
        Callq, [~$$"uf_connected"];
      ];
      text "main_end" [
        Movq, [~%Rbp; ~%Rsp];
        Movq, [Ind2 Rbp; ~%Rbp];
        Addq, [~$8; ~%Rsp];
        Retq, [];
      ];
      text "main_failure" [
        Movq, [~$1; ~%Rax];
        Jmp, [~$$"main_end"];
      ]
    ]  
  in
    [   
      ("uf3", program_test (uf 4) 1L);
      ("uf5", program_test (uf 5) 0L);
      ("uf10", program_test (uf 10) 0L);
      ("uf100", program_test (uf 100) 0L);  
    ]

(* Tests for Isaac Badipe (member of group 'Sigma Sigma On The Wall') *)
let isaac = 
  let imm_of_int x = Lit (Int64.of_int x) in
  let data_of_int x = Quad (imm_of_int x) in
  (* Accidentally wrote everything in reverse order, oops *)
  let operand_order_fixer {lbl; global; asm} =
    let new_asm =
      match asm with
      |  Data(_) -> asm
      |  Text(insts) -> let f (op, args:ins) = (op, List.rev args) in 
          Text(List.map f insts)
    in
    {lbl; global; asm = new_asm}
  in
  let convert_graph graph = Array.to_list graph |> List.map Array.to_list in
  let dfs (graph : int array array) (start : int) =
    let graph = convert_graph graph in
    let n = List.length graph in
    let flattened_graph = List.flatten graph in
    (* Test for edge in 2-D adjacency matrix *)
    List.map operand_order_fixer [ text "is_edge"
      [ Movq, [~%Rax; ~%Rsi]
      ; Imulq, [~%Rax; ~$(n * 8)]
      ; Imulq, [~%Rdx; ~$8]
      ; Addq, [~%Rax; ~%Rdx]
      ; Addq, [~%Rax; ~%Rdi]
      ; Movq, [~%Rax; Ind2 (Rax)]
      ; Andq, [~%Rax; ~$0xff]
      ; Retq, []
      ; ]
    (* 'Malloc' that uses a probably-free address in memory for data *)
    ; data "malloc_base" [data_of_int 0x408000]
    ; text "malloc"
      [ Movq, [~%Rax; Ind1 (Lbl "malloc_base")]
      ; Leaq, [~%Rsi; Ind1 (Lbl "malloc_base")]
      ; Addq, [Ind2 Rsi; ~%Rdi]
      ; Retq, []
      ]
    (* Graph and counter of connected vertices *)
    ; data "graph" (List.map data_of_int flattened_graph)
    ; data "connected_counter" [data_of_int 0]
    ; text "dfs_stub" (* Takes visited array pointer and vertex number *)
      [ Pushq, [~%Rbp]
      ; Movq, [~%Rbp; ~%Rsp]
      ; Subq, [~%Rsp; ~$16]
      (* Store in stack *)
      ; Movq, [Ind3 (Lit (-8L), Rbp); ~%Rsi]
      ; Movq, [Ind3 (Lit (-16L), Rbp); ~%Rdi]
      (* Check if already visited *)
      ; Movq, [~%Rax; ~%Rsi]
      ; Imulq, [~%Rax; ~$8]
      ; Addq, [~%Rax; ~%Rdi]
      ; Cmpq, [Ind2 Rax; ~$1]
      ; J Eq, [~$$"dfs_stub_end"] (* Already visited *)
      (* Set visited to true, increment counter *)
      ; Incq, [Ind1 (Lbl "connected_counter")]
      ; Movq, [Ind2 Rax; ~$1]
      ; Movq, [~%Rcx; ~$(-1)]
      ]
    ; text "loop"
      [ Incq, [~%Rcx]
      ; Cmpq, [~%Rcx; ~$n]
      ; J Ge, [~$$"dfs_stub_end"]
      ; Movq, [~%Rdi; ~$$"graph"]
      ; Movq, [~%Rsi; Ind3 (Lit (-8L), Rbp)]
      ; Movq, [~%Rdx; ~%Rcx]
      ; Callq, [~$$"is_edge"]
      ; Cmpq, [~%Rax; ~$1]
      ; J Neq, [~$$"loop"]
      ; Movq, [~%Rdi; Ind3 (Lit (-16L), Rbp)]
      ; Movq, [~%Rsi; ~%Rcx]
      ; Pushq, [~%Rcx]
      ; Callq, [~$$"dfs_stub"]
      ; Popq, [~%Rcx]
      ; Jmp, [~$$"loop"]
      ]
      ; text "dfs_stub_end"
      [
        Movq, [~%Rsp; ~%Rbp]
      ; Popq, [~%Rbp]
      ; Retq, []
      ]
    ; gtext "main"
      [ Movq, [~%Rdi; ~$(n * n * 8)]
      (* 'allocate' visited array *)
      ; Callq, [~$$"malloc"]
      ; Movq, [~%Rdi; ~%Rax]
      ; Movq, [~%Rsi; ~$start]
      (* Call recursive dfs stub *)
      ; Callq, [~$$"dfs_stub"]
      (* Return number of connected vertices *)
      ; Movq, [~%Rax; Ind1 (Lbl "connected_counter")]
      ; Retq, []
      ]
  ]
  in
  let new_graph n = Array.make_matrix n n 0 in
  (* Bidirectional and directional edge adding *)
  let (%>) graph (a, b) = graph.(a).(b) <- 1; graph in
  let (%%) graph (a, b) = graph %> (a, b) %> (b, a) in

  let graph1 = (new_graph 2) %% (0, 1) in
  let graph2 = (new_graph 3) %% (0, 1) %% (1, 2) in
  let graph3 = (new_graph 10) %% (0, 1) %% (1, 2) %% (2, 6) %% (2, 3) %% (2, 4)
  %% (5, 6) %% (7, 8) %% (8, 9) in
  let graph4 = (new_graph 5) %> (0, 1) %% (1, 2) in
  [
    ("dfs1", program_test (dfs graph1 0) 2L)
    ; ("dfs2", program_test (dfs graph2 0) 3L)
    ; ("dfs3", program_test (dfs graph3 0) 7L)
    ; ("dfs4", program_test (dfs graph3 5) 7L)
    ; ("dfs5", program_test (dfs graph3 8) 3L)
    ; ("dfs6", program_test (dfs graph4 0) 3L)
    ; ("dfs7", program_test (dfs graph4 1) 2L)
  ]

let student_tests = 
  [] 
  @ zkincaid (* Append your tests to this list *)
  @ satsuma
  @ arnav 
  @ richard_john  
  @ aepli_badoni
  @ isaac