open Ast

let rec interpret_expr (e : Ast.expr) : int =
  match e with
  | Eint(x) -> x
  | Ebinop(op, bob, john) ->
      let v1 = interpret_expr(bob) in
      let v2 = interpret_expr(john) in
      match op with
      | Minus -> v1 - v2
      | Plus -> v1 + v2
      | Div -> v1 / v2
      | Mult -> v1 * v2
