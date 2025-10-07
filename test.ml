(* test.ml *)
open OUnit2
open Assignment_7

(* Test resolution function with a basic Horn clause program *)
let test_resolution _ =
  let sig_ = [("p", 1); ("q", 1); ("r", 0)] in
  let clause1 = {head = C {node = "p"; children = [V "X"]}; body = [C {node = "q"; children = [V "X"]}]} in
  let clause2 = {head = C {node = "q"; children = [V "a"]}; body = []} in
  let program = [clause1; clause2] in
  let goal = [C {node = "p"; children = [V "a"]}] in
  let result = resolution goal program sig_ in
  assert_equal (true, [[(V "X", V "a")]]) result

(* More exhaustive test for complex goals and substitutions *)
let test_complex_resolution _ =
  let sig_ = [("ancestor", 2); ("parent", 2); ("john", 0); ("mary", 0); ("alice", 0)] in
  let clause1 = {head = C {node = "ancestor"; children = [V "X"; V "Y"]}; 
                 body = [C {node = "parent"; children = [V "X"; V "Y"]}]} in
  let clause2 = {head = C {node = "ancestor"; children = [V "X"; V "Y"]}; 
                 body = [C {node = "parent"; children = [V "X"; V "Z"]};
                            C {node = "ancestor"; children = [V "Z"; V "Y"]}]} in
  let clause3 = {head = C {node = "parent"; children = [C {node = "john"; children = []}; 
                                                        C {node = "mary"; children = []}]}; body = []} in
  let clause4 = {head = C {node = "parent"; children = [C {node = "mary"; children = []}; 
                                                        C {node = "alice"; children = []}]}; body = []} in
  let program = [clause1; clause2; clause3; clause4] in
  let goal = [C {node = "ancestor"; children = [C {node = "john"; children = []}; 
                                                C {node = "alice"; children = []}]}] in
  let result = resolution goal program sig_ in
  assert_equal (true, [[]]) result;

  let sig_1 = [("parent", 2); ("child", 2); ("john", 0); ("mary", 0); ("alice", 0); ("bob", 0)] in
  let clause1_1 = {head = C {node = "parent"; children = [C {node = "john"; children = []}; C {node = "mary"; children = []}]}; body = []} in
  let clause2_1 = {head = C {node = "parent"; children = [C {node = "mary"; children = []}; C {node = "alice"; children = []}]}; body = []} in
  let clause3_1 = {head = C {node = "child"; children = [C {node = "alice"; children = []}; C {node = "mary"; children = []}]}; body = []} in
  let program1 = [clause1_1; clause2_1; clause3_1] in
  let goal1 = [C {node = "parent"; children = [C {node = "john"; children = []}; C {node = "mary"; children = []}]}] in
  let result1 = resolution goal1 program1 sig_1 in
  assert_equal (true, [[]]) result1;

  let sig_2 = [("ancestor", 2); ("parent", 2); ("jane", 0); ("sara", 0); ("mark", 0); ("tom", 0)] in
  let clause1_2 = {head = C {node = "ancestor"; children = [V "X"; V "Y"]}; 
                  body = [C {node = "parent"; children = [V "X"; V "Y"]}]} in
  let clause2_2 = {head = C {node = "ancestor"; children = [V "X"; V "Y"]}; 
                  body = [C {node = "parent"; children = [V "X"; V "Z"]}; C {node = "ancestor"; children = [V "Z"; V "Y"]}]} in
  let clause3_2 = {head = C {node = "parent"; children = [C {node = "jane"; children = []}; C {node = "sara"; children = []}]}; body = []} in
  let clause4_2 = {head = C {node = "parent"; children = [C {node = "sara"; children = []}; C {node = "mark"; children = []}]}; body = []} in
  let clause5_2 = {head = C {node = "parent"; children = [C {node = "mark"; children = []}; C {node = "tom"; children = []}]}; body = []} in
  let program2 = [clause1_2; clause2_2; clause3_2; clause4_2; clause5_2] in
  let goal2 = [C {node = "ancestor"; children = [C {node = "jane"; children = []}; V "a"]}] in
  let result2 = resolution goal2 program2 sig_2 in
  assert_equal (true, [[(V "a", C {node = "sara"; children = []})]; [(V "a", C {node = "mark"; children = []})]; [(V "a", C {node = "tom"; children = []})]]) result2;

  let sig_3 = [("parent", 2); ("child", 2); ("adam", 0); ("eve", 0)] in
  let clause1_3 = {head = C {node = "parent"; children = [C {node = "adam"; children = []}; C {node = "eve"; children = []}]}; body = []} in
  let clause2_3 = {head = C {node = "child"; children = [C {node = "eve"; children = []}; C {node = "adam"; children = []}]}; body = []} in
  let program3 = [clause1_3; clause2_3] in
  let goal3 = [C {node = "parent"; children = [C {node = "eve"; children = []}; C {node = "adam"; children = []}]}] in
  let result3 = resolution goal3 program3 sig_3 in
  assert_equal (false, [[]]) result3;

  let sig_4 = [("sibling", 2); ("person1", 0); ("person2", 0); ("person3", 0)] in
  let clause1_4 = {head = C {node = "sibling"; children = [C {node = "person1"; children = []}; C {node = "person2"; children = []}]}; body = []} in
  let clause2_4 = {head = C {node = "sibling"; children = [C {node = "person1"; children = []}; C {node = "person3"; children = []}]}; body = []} in
  let program4 = [clause1_4; clause2_4] in
  let goal4 = [C {node = "sibling"; children = [C {node = "person1"; children = []}; V "Y"]}] in
  let result4 = resolution goal4 program4 sig_4 in
  assert_equal (true, [[(V "Y", C {node = "person2"; children = []})]; [(V "Y", C {node = "person3"; children = []})]]) result4

(* Test suite *)
let suite =
  "Prolog Interpreter Tests" >::: [
    "test_resolution" >:: test_resolution;
    "test_complex_resolution" >:: test_complex_resolution;
  ]

let () =
  run_test_tt_main suite
