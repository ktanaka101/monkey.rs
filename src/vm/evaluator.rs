use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;

use anyhow::Result;

use crate::parser::{ast, tools};

use super::builtin::{Function, FALSE, NULL, TRUE};
use super::env::Environment;
use super::object;

pub fn eval_node(node: &ast::Node, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    match node {
        ast::Node::Program(n) => eval_program(n, Rc::clone(&env)),
        ast::Node::Stmt(stmt) => eval_stmt(stmt, Rc::clone(&env)),
        ast::Node::Expr(expr) => eval_expr(expr, Rc::clone(&env)),
    }
}
fn eval_stmt(stmt: &ast::Stmt, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    match stmt {
        ast::Stmt::ExprStmt(stmt) => eval_expr(&stmt.expr, Rc::clone(&env)),
        ast::Stmt::Let(stmt) => {
            let val = eval_expr(&stmt.value, Rc::clone(&env))?;
            env.borrow_mut().insert(&stmt.name.value, val);
            Ok(NULL.into())
        }
        ast::Stmt::Block(stmt) => eval_block(stmt, Rc::clone(&env)),
        ast::Stmt::Return(stmt) => {
            let val = eval_expr(&stmt.return_value, Rc::clone(&env))?;
            Ok(object::Return {
                value: Box::new(val),
            }
            .into())
        }
    }
}
fn eval_expr(expr: &ast::Expr, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    match expr {
        ast::Expr::Array(expr) => {
            let elements = eval_expressions(&expr.elements, Rc::clone(&env))?;
            Ok(object::Array { elements }.into())
        }
        ast::Expr::Boolean(expr) => Ok(native_bool_to_boolean_object(expr.value)),
        ast::Expr::Call(expr) => {
            if expr.func.to_string() == "quote" {
                return quote(ast::Node::Expr(expr.args[0].clone()), Rc::clone(&env));
            }

            let func = eval_expr(&expr.func, Rc::clone(&env))?;
            let args = eval_expressions(&expr.args, Rc::clone(&env))?;
            Ok(apply_function(&func, &args)?)
        }
        ast::Expr::Function(expr) => Ok(object::Function {
            params: expr.params.clone(),
            body: expr.body.clone(),
            env: Rc::clone(&env),
        }
        .into()),
        ast::Expr::Hash(expr) => Ok(eval_hash_literal(&expr, Rc::clone(&env))?),
        ast::Expr::Identifier(expr) => Ok(eval_identifier(&expr, Rc::clone(&env))?),
        ast::Expr::If(expr) => Ok(eval_if_expr(&expr, Rc::clone(&env))?),
        ast::Expr::Index(expr) => {
            let left = eval_expr(&expr.left, Rc::clone(&env))?;
            let index = eval_expr(&expr.index, Rc::clone(&env))?;
            // TOOD: clone to reference
            Ok(eval_index_expr(&left, &index)?.clone())
        }
        ast::Expr::InfixExpr(expr) => {
            let left = eval_expr(&expr.left, Rc::clone(&env))?;
            let right = eval_expr(&expr.right, Rc::clone(&env))?;
            Ok(eval_infix_expr(&expr.ope, &left, &right)?)
        }
        ast::Expr::Integer(expr) => Ok(object::Integer { value: expr.value }.into()),
        ast::Expr::PrefixExpr(expr) => {
            let right = eval_expr(&expr.right, Rc::clone(&env))?;
            Ok(eval_prefix_expr(&expr.ope, &right)?)
        }
        ast::Expr::StringLit(expr) => Ok(object::StringLit {
            value: expr.value.clone(),
        }
        .into()),
    }
}

pub(crate) fn new_error<T>(message: &str) -> Result<T> {
    Err(object::Error::Eval(message.into()))?
}

fn eval_program(program: &ast::Program, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let mut obj: object::Object = NULL.into();
    for stmt in program.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            object::Object::Return(r) => return Ok(r.value.as_ref().clone()),
            o => obj = o,
        }
    }

    Ok(obj)
}

fn eval_block(block: &ast::Block, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let mut obj: object::Object = NULL.into();
    for stmt in block.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            object::Object::Return(r) => return Ok(r.into()),
            o => obj = o,
        }
    }

    Ok(obj)
}

fn eval_prefix_expr(ope: &ast::Operator, right: &object::Object) -> Result<object::Object> {
    match ope {
        ast::Operator::Bang => Ok(eval_bang_ope_expr(right)),
        ast::Operator::Minus => Ok(eval_minus_prefix_ope_expr(right)?),
        unknown => new_error(&format!("unknown operator: {} {}", unknown, right.o_type()))?,
    }
}

fn native_bool_to_boolean_object(input: bool) -> object::Object {
    object::Object::Boolean(if input { TRUE } else { FALSE })
}

fn eval_bang_ope_expr(right: &object::Object) -> object::Object {
    object::Object::Boolean(match right {
        object::Object::Boolean(b) => match b {
            _ if b == &TRUE => FALSE,
            _ if b == &FALSE => TRUE,
            _ => unreachable!(),
        },
        object::Object::Null(_) => TRUE,
        _ => FALSE,
    })
}

fn eval_minus_prefix_ope_expr(right: &object::Object) -> Result<object::Object> {
    match right {
        object::Object::Integer(i) => {
            let value = match i.value.checked_neg() {
                Some(v) => v,
                None => new_error(&format!("overflow: {}", i))?,
            };
            Ok(object::Integer { value }.into())
        }
        unknown => new_error(&format!("unknown operator: -{}", unknown.o_type())),
    }
}

fn eval_infix_expr(
    ope: &ast::Operator,
    left: &object::Object,
    right: &object::Object,
) -> Result<object::Object> {
    match (ope, left, right) {
        (o, object::Object::Integer(l), object::Object::Integer(r)) => {
            eval_integer_infix_expr(o, l, r)
        }
        (o, object::Object::StringLit(l), object::Object::StringLit(r)) => {
            eval_string_infix_expr(o, l, r)
        }
        (ast::Operator::Equal, l, r) => Ok(native_bool_to_boolean_object(l == r)),
        (ast::Operator::NotEqual, l, r) => Ok(native_bool_to_boolean_object(l != r)),
        (o, l, r) => {
            if l.o_type() == r.o_type() {
                new_error(&format!(
                    "unknown operator: {} {} {}",
                    l.o_type(),
                    o,
                    r.o_type()
                ))?
            } else {
                new_error(&format!(
                    "type mismatch: {} {} {}",
                    l.o_type(),
                    o,
                    r.o_type()
                ))?
            }
        }
    }
}

fn eval_integer_infix_expr(
    ope: &ast::Operator,
    left: &object::Integer,
    right: &object::Integer,
) -> Result<object::Object> {
    use ast::Operator::*;
    let res = match ope {
        Plus => {
            let value = match left.value.checked_add(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} + {}", left.value, right.value))?,
            };
            object::Integer { value }.into()
        }
        Minus => {
            let value = match left.value.checked_sub(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            object::Integer { value }.into()
        }
        Asterisk => {
            let value = match left.value.checked_mul(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            object::Integer { value }.into()
        }
        Slash => {
            let value = match left.value.checked_div(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            object::Integer { value }.into()
        }
        Lt => native_bool_to_boolean_object(left.value < right.value),
        Gt => native_bool_to_boolean_object(left.value > right.value),
        Equal => native_bool_to_boolean_object(left.value == right.value),
        NotEqual => native_bool_to_boolean_object(left.value != right.value),
        unknown => new_error(&format!("unknown operator: {}", unknown))?,
    };

    Ok(res)
}

fn eval_string_infix_expr(
    ope: &ast::Operator,
    left: &object::StringLit,
    right: &object::StringLit,
) -> Result<object::Object> {
    match ope {
        ast::Operator::Plus => {
            let mut value = left.value.clone();
            value.push_str(&right.value);
            Ok(object::StringLit { value }.into())
        }
        unknown => new_error(&format!("unknown operator: String {} String", unknown)),
    }
}

fn eval_if_expr(if_expr: &ast::If, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let cond = eval_expr(if_expr.cond.as_ref(), Rc::clone(&env))?;

    if is_truthy(cond) {
        eval_stmt(
            &ast::Stmt::Block(if_expr.consequence.clone()),
            Rc::clone(&env),
        )
    } else if let Some(alt) = &if_expr.alternative {
        eval_stmt(&ast::Stmt::Block(alt.clone()), env)
    } else {
        Ok(NULL.into())
    }
}

fn is_truthy(obj: object::Object) -> bool {
    match obj {
        object::Object::Null(_) => false,
        object::Object::Boolean(b) => match b {
            _ if b == TRUE => true,
            _ if b == FALSE => false,
            _ => unreachable!(),
        },
        _ => true,
    }
}

fn eval_identifier(
    node: &ast::Identifier,
    env: Rc<RefCell<Environment>>,
) -> Result<object::Object> {
    let cur_env = env.borrow_mut();
    let ident = cur_env.get(&node.value);
    if let Some(id) = ident {
        return Ok(id);
    }

    let builtin = Function::try_from(node.value.as_str());
    if let Ok(builtin) = builtin {
        return Ok(builtin.into());
    }

    new_error(&format!("identifier not found: {}", node.value))
}

fn eval_expressions(
    expr_list: &[ast::Expr],
    env: Rc<RefCell<Environment>>,
) -> Result<Vec<object::Object>> {
    let mut result = Vec::<object::Object>::new();

    for expr in expr_list.iter() {
        result.push(eval_expr(expr, Rc::clone(&env))?);
    }

    Ok(result)
}

fn apply_function(func: &object::Object, args: &[object::Object]) -> Result<object::Object> {
    match func {
        object::Object::Function(f) => {
            let extended_env = extend_function_env(f, args)?;
            let evaluated = eval_stmt(&f.body.clone().into(), extended_env)?;
            Ok(unwrap_return_value(&evaluated))
        }
        object::Object::Builtin(builtin) => builtin.call(args),
        invalid => new_error(&format!("not a function: {}", invalid.o_type())),
    }
}

fn extend_function_env(
    func: &object::Function,
    args: &[object::Object],
) -> Result<Rc<RefCell<Environment>>> {
    let mut env = Environment::new_enclose(Rc::clone(&func.env));

    for (i, param) in func.params.iter().enumerate() {
        let arg = match args.get(i) {
            Some(arg) => arg,
            None => new_error("not found arg.")?,
        };
        env.insert(&param.value, arg.clone());
    }

    Ok(Rc::new(RefCell::new(env)))
}

fn unwrap_return_value(obj: &object::Object) -> object::Object {
    match obj.clone() {
        object::Object::Return(o) => o.into(),
        o => o,
    }
}

fn eval_index_expr<'a>(
    left: &'a object::Object,
    index: &object::Object,
) -> Result<&'a object::Object> {
    match (left, index) {
        (object::Object::Array(l), object::Object::Integer(idx)) => {
            Ok(eval_array_index_expr(l, idx)?)
        }
        (object::Object::Hash(l), idx) => Ok(eval_hash_index_expr(l, idx)?),
        (l, _) => new_error(&format!("index operator not supported: {}", l.o_type()))?,
    }
}

fn eval_array_index_expr<'a>(
    array: &'a object::Array,
    index: &object::Integer,
) -> Result<&'a object::Object> {
    if index.value < 0 {
        return Ok(&object::Object::Null(NULL));
    }
    let idx = usize::try_from(index.value).or_else(|e| new_error(&e.to_string()))?;

    match array.elements.get(idx) {
        Some(obj) => Ok(obj),
        None => Ok(&object::Object::Null(NULL)),
    }
}

fn eval_hash_literal(node: &ast::Hash, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let mut pairs = object::HashPairs::new();

    for pair in node.pairs.iter() {
        let key = eval_expr(&pair.key, Rc::clone(&env))?;
        let value = eval_expr(&pair.value, Rc::clone(&env))?;
        let key_type = key.o_type();

        match object::HashableObject::try_from(key) {
            Ok(o) => pairs.insert(o, value),
            Err(_) => new_error(&format!("unusable as hash key: {}", key_type))?,
        };
    }

    Ok(object::Hash { pairs }.into())
}

fn eval_hash_index_expr<'a>(
    hash: &'a object::Hash,
    key: &object::Object,
) -> Result<&'a object::Object> {
    let key_type = key.o_type();
    match object::HashableObject::try_from(key.clone()) {
        Ok(o) => Ok(match hash.pairs.get(&o) {
            Some(value) => &value,
            None => &object::Object::Null(NULL),
        }),
        Err(_) => new_error(&format!("unusable as hash key: {}", key_type))?,
    }
}

fn quote(node: ast::Node, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let node = eval_unquote_calls(node, env)?;
    Ok(object::Quote { node }.into())
}

fn eval_unquote_calls(quoted: ast::Node, env: Rc<RefCell<Environment>>) -> Result<ast::Node> {
    tools::modify(quoted, |node: ast::Node| -> Result<ast::Node> {
        if !is_unquote_call(&node) {
            return Ok(node);
        }

        match &node {
            ast::Node::Expr(ast::Expr::Call(call)) => {
                if call.args.len() == 1 {
                    let arg = call.args[0].clone();
                    Ok(convert_object_to_ast_node(eval_node(
                        &arg.into(),
                        Rc::clone(&env),
                    )?))
                } else {
                    unimplemented!()
                }
            }
            _ => unimplemented!(),
        }
    })
}

fn convert_object_to_ast_node(obj: object::Object) -> ast::Node {
    match obj {
        object::Object::Integer(int) => ast::Expr::from(ast::Integer { value: int.value }).into(),
        object::Object::Boolean(b) => ast::Expr::from(ast::Boolean { value: b.value }).into(),
        object::Object::Quote(q) => q.node,
        _ => unimplemented!(),
    }
}

fn is_unquote_call(node: &ast::Node) -> bool {
    match node {
        ast::Node::Expr(ast::Expr::Call(call)) => (*call.func).to_string() == "unquote",
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_integer_expression() {
        let tests = vec![
            ("5", 5_i64),
            ("5", 5_i64),
            ("10", 10_i64),
            ("-5", -5_i64),
            ("-10", -10_i64),
            ("5 + 5 + 5 + 5 - 10", 10_i64),
            ("2 * 2 * 2 * 2 * 2", 32_i64),
            ("-50 + 100 + -50", 0_i64),
            ("5 * 2 + 10", 20_i64),
            ("5 + 2 * 10", 25_i64),
            ("20 + 2 * -10", 0_i64),
            ("50 / 2 * 2 + 10", 60_i64),
            ("2 * (5 + 10)", 30_i64),
            ("3 * 3 * 3 + 10", 37_i64),
            ("3 * (3 * 3) + 10", 37_i64),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50_i64),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));
    }

    #[test]
    fn test_eval_boolean_expression() {
        let tests = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_boolean_object(eval(input), expected));
    }

    #[test]
    fn test_bang_operator() {
        let tests = vec![
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_boolean_object(eval(input), expected));
    }

    #[test]
    fn test_if_else_expression() {
        let tests = vec![
            ("if (true) { 10 }", 10_i64),
            ("if (1) { 10 }", 10_i64),
            ("if ( 1 < 2 ) { 10 }", 10_i64),
            ("if ( 1 > 2 ) { 10 } else { 20 }", 20_i64),
            ("if ( 1 < 2 ) { 10 } else { 20 }", 10_i64),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec!["if (false) { 10 }", "if ( 1 > 2 ) { 10 }"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));
    }

    #[test]
    fn test_return_statements() {
        let tests = vec![
            ("return 10;", 10_i64),
            ("return 10; 9;", 10_i64),
            ("return 2 * 5; 9;", 10_i64),
            ("9; return 2 * 5; 9;", 10_i64),
            (
                r#"
                    if (10 > 1) {
                        if (10 > 1) {
                            return 10;
                        }
                    }

                    retrun 1;
                "#,
                10_i64,
            ),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));
    }

    #[test]
    fn test_error_handling() {
        let tests = vec![
            ("5 + true;", "type mismatch: Integer + Boolean"),
            ("5 + true; 5;", "type mismatch: Integer + Boolean"),
            ("-true", "unknown operator: -Boolean"),
            ("true + false;", "unknown operator: Boolean + Boolean"),
            ("5; true + false; 5", "unknown operator: Boolean + Boolean"),
            (
                "if (10 > 1 ) { true + false; }",
                "unknown operator: Boolean + Boolean",
            ),
            (
                r#"
                if (10 > 1) {
                if (10 > 1) {
                    return true + false;
                }
                return 1;
                }
            "#,
                "unknown operator: Boolean + Boolean",
            ),
            ("foobar", "identifier not found: foobar"),
            (r#""Hello" - "World""#, "unknown operator: String - String"),
            (
                r#"{"name": "Monkey"}[fn(x) { x }];"#,
                "unusable as hash key: Function",
            ),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_let_statements() {
        let tests = vec![
            ("let a = 5; a;", 5_i64),
            ("let a = 5 * 5; a;", 25_i64),
            ("let a = 5; let b = a; b;", 5_i64),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15_i64),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));
    }

    #[test]
    fn test_function_object() {
        let tests = vec![("fn(x) { x + 2; };", 1, "x", "{ (x + 2) }")];
        tests.into_iter().for_each(
            |(input, expected_params_size, expected_params, expected_body)| {
                let obj = eval(input);
                match obj {
                    object::Object::Function(o) => {
                        assert_eq!(o.params.len(), expected_params_size);
                        assert_eq!(o.params[0].to_string(), expected_params);
                        assert_eq!(o.body.to_string(), expected_body);
                    }
                    o => panic!(format!("expected Function. received {}", o)),
                }
            },
        );
    }

    #[test]
    fn test_function_application() {
        let tests = vec![
            ("let identity = fn(x) { x; }; identity(5);", 5_i64),
            ("let identity = fn(x) { return x; }; identity(5);", 5_i64),
            ("let double = fn(x) { x * 2; }; double(5);", 10_i64),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10_i64),
            (
                "let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));",
                20_i64,
            ),
            ("fn(x) { x; }(5)", 5_i64),
            (
                r#"
                    let add = fn(a, b) { a + b };
                    let sub = fn(a, b) { a - b };
                    let apply_func = fn(a, b, func) { func(a, b) };
                    apply_func(2, 2, add);
                "#,
                4_i64,
            ),
            (
                r#"
                    let add = fn(a, b) { a + b };
                    let sub = fn(a, b) { a - b };
                    let apply_func = fn(a, b, func) { func(a, b) };
                    apply_func(10, 2, sub);
                "#,
                8_i64,
            ),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));
    }

    #[test]
    fn test_closures() {
        let tests = vec![(
            r#"
                    let new_addr = fn(x) {
                    fn(y) { x + y};
                    }

                    let addTwo = new_addr(2);
                    addTwo(2);
                "#,
            4_i64,
        )];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));
    }

    #[test]
    fn test_string_literal() {
        let tests = vec![(r#""Hello World!""#, "Hello World!")];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_string_object(eval(input), expected));
    }

    #[test]
    fn test_string_concatenation() {
        let tests = vec![(r#""Hello" + " " + "World!""#, "Hello World!")];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_string_object(eval(input), expected));
    }

    #[test]
    fn test_builtin_function_len() {
        let tests = vec![
            (r#"len("")"#, 0_i64),
            (r#"len("four")"#, 4_i64),
            (r#"len("hello world")"#, 11_i64),
            ("len([])", 0_i64),
            (r#"len([1, "hello", 33])"#, 3_i64),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec![
            ("len(1)", "argument to 'len' not supported, got Integer"),
            (
                r#"len("one", "two")"#,
                "wrong number of arguments. got=2, want=1",
            ),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_builtin_function_first() {
        let tests = vec![("first([1, 2, 3])", 1_i64)];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec![(r#"first(["one", "two"])"#, "one")];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_string_object(eval(input), expected));

        let tests = vec!["first([])"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));

        let tests = vec![("let a = [1, 2, 3]; first(a); first(a) == first(a)", true)];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_boolean_object(eval(input), expected));

        let tests = vec![
            (
                "first([1, 2, 3], [1, 2, 3])",
                "wrong number of arguments. got=2, want=1",
            ),
            ("first(1)", "argument to 'first' must be Array, got Integer"),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_builtin_function_last() {
        let tests = vec![("last([1, 2, 3])", 3_i64)];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec![(r#"last(["one", "two"])"#, "two")];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_string_object(eval(input), expected));

        let tests = vec!["last([])"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));

        let tests = vec![("let a = [1, 2, 3]; last(a); last(a) == last(a)", true)];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_boolean_object(eval(input), expected));

        let tests = vec![
            (
                "last([1, 2, 3], [1, 2, 3])",
                "wrong number of arguments. got=2, want=1",
            ),
            ("last(1)", "argument to 'last' must be Array, got Integer"),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_builtin_function_rest() {
        let tests = vec![("rest([1, 2, 3])", [2_i64, 3_i64])];
        tests.into_iter().for_each(|(input, expected)| {
            assert_integer_array_object(eval(input), expected.to_vec())
        });

        let tests = vec![(r#"rest(["one", "two"])"#, ["two"])];
        tests.into_iter().for_each(|(input, expected)| {
            assert_string_array_object(eval(input), expected.to_vec())
        });

        let tests = vec!["rest([])"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));

        let tests = vec![("let a = [1, 2, 3, 4]; rest(rest(a));", [3_i64, 4_i64])];
        tests.into_iter().for_each(|(input, expected)| {
            assert_integer_array_object(eval(input), expected.to_vec())
        });

        let tests = vec!["let a = [1, 2, 3, 4]; rest(rest(a)); rest(rest(rest(rest(rest(a)))));"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));

        let tests = vec![
            (
                "rest([1, 2, 3], [1, 2, 3])",
                "wrong number of arguments. got=2, want=1",
            ),
            ("rest(1)", "argument to 'rest' must be Array, got Integer"),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_builtin_function_push() {
        let tests = vec![
            ("push([1, 2, 3], 4)", vec![1_i64, 2_i64, 3_i64, 4_i64]),
            ("push([1, 2, 3], 3)", vec![1_i64, 2_i64, 3_i64, 3_i64]),
            ("push([], 1)", vec![1_i64]),
            (
                "let a = [1, 2]; push(push(a, 3), 4);",
                vec![1_i64, 2_i64, 3_i64, 4_i64],
            ),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_integer_array_object(eval(input), expected.into())
        });

        let input = "push([1, 2, 3], [4, 5])";
        let expected1 = 1_i64;
        let expected2 = 2_i64;
        let expected3 = 3_i64;
        let expected4 = vec![4_i64, 5_i64];
        let evaluated = eval(input);
        match evaluated {
            object::Object::Array(o) => {
                assert_eq!(o.elements.len(), 4);
                assert_integer_object(o.elements[0].clone(), expected1);
                assert_integer_object(o.elements[1].clone(), expected2);
                assert_integer_object(o.elements[2].clone(), expected3);
                assert_integer_array_object(o.elements[3].clone(), expected4)
            }
            o => panic!(format!("expected Array, received {:?}.", o)),
        }

        let tests = vec![
            (
                "push([1, 2, 3], 1, 2)",
                "wrong number of arguments. got=3, want=2",
            ),
            (
                "push(1, 2)",
                "argument to 'push' must be Array, got Integer",
            ),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            assert_error_object(eval_non_check(input).unwrap_err(), expected)
        });
    }

    #[test]
    fn test_array_literal() {
        let tests = vec![("[1, 2 * 2, 3 + 3]", vec![1_i64, 4_i64, 6_i64])];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_array_object(eval(input), expected));
    }

    #[test]
    fn test_array_index_expression() {
        let tests = vec![
            ("[1, 2, 3][0]", 1_i64),
            ("[1, 2, 3][1]", 2_i64),
            ("[1, 2, 3][2]", 3_i64),
            ("let i = 0; [1][i];", 1_i64),
            ("[1, 2, 3][1 + 1];", 3_i64),
            ("let myArray = [1, 2, 3]; myArray[2];", 3_i64),
            (
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
                6_i64,
            ),
            (
                "let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i];",
                2_i64,
            ),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec!["[1, 2, 3][3]", "[1, 2, 3][-1]"];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));
    }

    #[test]
    fn test_hash_literal() {
        let input = r#"
            let two = "two";
            {
                "one": 10 - 9,
                two: 1 + 1,
                "thr" + "ee": 6 / 2,
                4: 4,
                true: 5,
                false: 6
            }
        "#;

        let evaluated = eval(input);
        match evaluated {
            object::Object::Hash(evaluated) => {
                assert_eq!(evaluated.pairs.len(), 6);

                let expected = vec![
                    (
                        object::HashableObject::try_from(object::Object::from(object::StringLit {
                            value: "one".into(),
                        }))
                        .unwrap(),
                        1_i64,
                    ),
                    (
                        object::HashableObject::try_from(object::Object::from(object::StringLit {
                            value: "two".into(),
                        }))
                        .unwrap(),
                        2_i64,
                    ),
                    (
                        object::HashableObject::try_from(object::Object::from(object::StringLit {
                            value: "three".into(),
                        }))
                        .unwrap(),
                        3_i64,
                    ),
                    (
                        object::HashableObject::try_from(object::Object::from(object::Integer {
                            value: 4_i64,
                        }))
                        .unwrap(),
                        4_i64,
                    ),
                    (
                        object::HashableObject::try_from(object::Object::from(object::Boolean {
                            value: true,
                        }))
                        .unwrap(),
                        5_i64,
                    ),
                    (
                        object::HashableObject::try_from(object::Object::from(object::Boolean {
                            value: false,
                        }))
                        .unwrap(),
                        6_i64,
                    ),
                ];
                expected
                    .into_iter()
                    .for_each(|(expected_key, expected_value)| {
                        let value = evaluated.pairs.get(&expected_key).unwrap();
                        assert_integer_object(value.clone(), expected_value);
                    });
            }
            o => panic!(format!("expected Hash. received {:?}", o)),
        }
    }

    #[test]
    fn test_hash_index_expression() {
        let tests = vec![
            (r#"{"foo": 5}["foo"]"#, 5_i64),
            (r#"let key = "foo"; {"foo": 5}[key]"#, 5_i64),
            ("{5: 5}[5]", 5_i64),
            ("{true: 5}[true]", 5_i64),
            ("{false: 5}[false]", 5_i64),
        ];
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_object(eval(input), expected));

        let tests = vec![(r#"{"foo": 5}["bar"]"#), (r#"{}["foo"]"#)];
        tests
            .into_iter()
            .for_each(|input| assert_null_object(eval(input)));
    }

    #[test]
    fn test_quote() {
        let tests = vec![
            ("quote(5)", "5"),
            ("quote(5 + 8)", "(5 + 8)"),
            ("quote(foobar)", "foobar"),
            ("quote(foobar + barfoo)", "(foobar + barfoo)"),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            let evaluated = eval(input);
            match evaluated {
                object::Object::Quote(o) => assert_eq!(o.to_string(), expected),
                o => panic!(format!("expected Quote. received {:?}", o)),
            }
        });
    }

    #[test]
    fn test_quote_unquote() {
        let tests = vec![
            ("quote(unquote(4))", "4"),
            ("quote(unquote(4 + 4))", "8"),
            ("quote(8 + unquote(4 + 4))", "(8 + 8)"),
            ("quote(unquote(4 + 4) + 8)", "(8 + 8)"),
            (
                "
                    let foobar = 8;
                    quote(foobar)
                ",
                "foobar",
            ),
            (
                "
                    let foobar = 8;
                    quote(unquote(foobar))
                ",
                "8",
            ),
            ("quote(unquote(true))", "true"),
            ("quote(unquote(true == false))", "false"),
            ("quote(unquote(quote(4 + 4)))", "(4 + 4)"),
            (
                "
                    let quotedInfixExpression = quote(4 + 4);
                    quote(unquote(4 + 4) + unquote(quotedInfixExpression))
                ",
                "(8 + (4 + 4))",
            ),
        ];
        tests.into_iter().for_each(|(input, expected)| {
            let evaluated = eval(input);
            match evaluated {
                object::Object::Quote(o) => assert_eq!(o.to_string(), expected),
                o => panic!(format!("expected Quote. received {:?}", o)),
            }
        });
    }

    fn check_err_and_unrwap<T, E>(result: std::result::Result<T, E>, input: &str) -> T
    where
        E: std::fmt::Debug,
    {
        result
            .map_err(move |e| format!("{} //=> {:?}", input, e))
            .unwrap()
    }

    fn eval(input: &str) -> object::Object {
        let evaluated = eval_non_check(input);
        check_err_and_unrwap(evaluated, input)
    }

    fn eval_non_check(input: &str) -> Result<object::Object> {
        let l = crate::lexer::Lexer::new(input.to_string());
        let mut p = crate::parser::Parser::new(l);

        let program = p.parse_program();
        let program = check_err_and_unrwap(program, input);

        let env = Rc::new(RefCell::new(Environment::new(None)));
        eval_program(&program, env)
    }

    fn assert_integer_object(obj: object::Object, expected: i64) {
        match obj {
            object::Object::Integer(o) => assert_eq!(o.value, expected),
            o => panic!(format!("expected Integer. received {:?}", o)),
        }
    }

    fn assert_boolean_object(obj: object::Object, expected: bool) {
        match obj {
            object::Object::Boolean(o) => assert_eq!(o.value, expected),
            o => panic!(format!("expected Boolean. received {:?}", o)),
        }
    }

    fn assert_null_object(obj: object::Object) {
        match obj {
            object::Object::Null(_) => (),
            o => panic!(format!("expected Null. received {:?}", o)),
        }
    }

    fn assert_error_object(err: anyhow::Error, expected: &str) {
        assert_eq!(err.to_string(), expected)
    }

    fn assert_string_object(obj: object::Object, expected: &str) {
        match obj {
            object::Object::StringLit(o) => assert_eq!(o.value, expected),
            o => panic!(format!("expected StringLit. received {:?}", o)),
        }
    }

    fn assert_integer_array_object(obj: object::Object, expected_arr: Vec<i64>) {
        match obj {
            object::Object::Array(o) => {
                assert_eq!(o.elements.len(), expected_arr.len());

                expected_arr
                    .into_iter()
                    .zip(o.elements)
                    .for_each(|(expected, ele)| match ele {
                        object::Object::Integer(o) => assert_eq!(o.value, expected),
                        o => panic!(format!("expected Array<Integer>. received {:?}", o)),
                    })
            }
            o => panic!(format!("expected Array<Integer>. received {:?}", o)),
        }
    }

    fn assert_string_array_object(obj: object::Object, expected_arr: Vec<&str>) {
        match obj {
            object::Object::Array(o) => {
                assert_eq!(o.elements.len(), expected_arr.len());

                expected_arr
                    .into_iter()
                    .zip(o.elements)
                    .for_each(|(expected, ele)| match ele {
                        object::Object::StringLit(o) => assert_eq!(o.value, expected),
                        o => panic!(format!("expected Array<Integer>. received {:?}", o)),
                    })
            }
            o => panic!(format!("expected Array<Integer>. received {:?}", o)),
        }
    }
}
