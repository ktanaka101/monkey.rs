pub mod builtin;
pub mod env;
pub mod objects;

use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;

use anyhow::Result;

use crate::parser::{ast, tools};

use crate::evaluator::builtin::{Function, FALSE, NULL, TRUE};
use crate::evaluator::env::Environment;

pub fn eval_node(node: &ast::Node, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    match node {
        ast::Node::Program(n) => eval_program(n, Rc::clone(&env)),
        ast::Node::Stmt(stmt) => eval_stmt(stmt, Rc::clone(&env)),
        ast::Node::Expr(expr) => eval_expr(expr, Rc::clone(&env)),
    }
}
fn eval_stmt(stmt: &ast::Stmt, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
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
            Ok(objects::Return {
                value: Box::new(val),
            }
            .into())
        }
    }
}
fn eval_expr(expr: &ast::Expr, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    match expr {
        ast::Expr::Array(expr) => {
            let elements = eval_expressions(&expr.elements, Rc::clone(&env))?;
            Ok(objects::Array { elements }.into())
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
        ast::Expr::Function(expr) => Ok(objects::Function {
            params: expr.params.clone(),
            body: expr.body.clone(),
            env: Rc::clone(&env),
        }
        .into()),
        ast::Expr::Hash(expr) => Ok(eval_hash_literal(expr, Rc::clone(&env))?),
        ast::Expr::Identifier(expr) => Ok(eval_identifier(expr, Rc::clone(&env))?),
        ast::Expr::If(expr) => Ok(eval_if_expr(expr, Rc::clone(&env))?),
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
        ast::Expr::Integer(expr) => Ok(objects::Integer { value: expr.value }.into()),
        ast::Expr::PrefixExpr(expr) => {
            let right = eval_expr(&expr.right, Rc::clone(&env))?;
            Ok(eval_prefix_expr(&expr.ope, &right)?)
        }
        ast::Expr::StringLit(expr) => Ok(objects::StringLit {
            value: expr.value.clone(),
        }
        .into()),
        _ => unreachable!(),
    }
}

pub(crate) fn new_error<T>(message: &str) -> Result<T> {
    Err(objects::Error::Standard(message.into()).into())
}

fn eval_program(program: &ast::Program, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    let mut obj: objects::Object = NULL.into();
    for stmt in program.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            objects::Object::Return(r) => return Ok(r.value.as_ref().clone()),
            o => obj = o,
        }
    }

    Ok(obj)
}

fn eval_block(block: &ast::Block, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    let mut obj: objects::Object = NULL.into();
    for stmt in block.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            objects::Object::Return(r) => return Ok(r.into()),
            o => obj = o,
        }
    }

    Ok(obj)
}

fn eval_prefix_expr(ope: &ast::Operator, right: &objects::Object) -> Result<objects::Object> {
    match ope {
        ast::Operator::Bang => Ok(eval_bang_ope_expr(right)),
        ast::Operator::Minus => Ok(eval_minus_prefix_ope_expr(right)?),
        unknown => new_error(&format!("unknown operator: {} {}", unknown, right.o_type()))?,
    }
}

fn native_bool_to_boolean_object(input: bool) -> objects::Object {
    objects::Object::Boolean(if input { TRUE } else { FALSE })
}

fn eval_bang_ope_expr(right: &objects::Object) -> objects::Object {
    objects::Object::Boolean(match right {
        objects::Object::Boolean(b) => match b {
            _ if b == &TRUE => FALSE,
            _ if b == &FALSE => TRUE,
            _ => unreachable!(),
        },
        objects::Object::Null(_) => TRUE,
        _ => FALSE,
    })
}

fn eval_minus_prefix_ope_expr(right: &objects::Object) -> Result<objects::Object> {
    match right {
        objects::Object::Integer(i) => {
            let value = match i.value.checked_neg() {
                Some(v) => v,
                None => new_error(&format!("overflow: {}", i))?,
            };
            Ok(objects::Integer { value }.into())
        }
        unknown => new_error(&format!("unknown operator: -{}", unknown.o_type())),
    }
}

fn eval_infix_expr(
    ope: &ast::Operator,
    left: &objects::Object,
    right: &objects::Object,
) -> Result<objects::Object> {
    match (ope, left, right) {
        (o, objects::Object::Integer(l), objects::Object::Integer(r)) => {
            eval_integer_infix_expr(o, l, r)
        }
        (o, objects::Object::StringLit(l), objects::Object::StringLit(r)) => {
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
    left: &objects::Integer,
    right: &objects::Integer,
) -> Result<objects::Object> {
    use ast::Operator::*;
    let res = match ope {
        Plus => {
            let value = match left.value.checked_add(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} + {}", left.value, right.value))?,
            };
            objects::Integer { value }.into()
        }
        Minus => {
            let value = match left.value.checked_sub(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            objects::Integer { value }.into()
        }
        Asterisk => {
            let value = match left.value.checked_mul(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            objects::Integer { value }.into()
        }
        Slash => {
            let value = match left.value.checked_div(right.value) {
                Some(v) => v,
                None => new_error(&format!("overflow: {} - {}", left.value, right.value))?,
            };
            objects::Integer { value }.into()
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
    left: &objects::StringLit,
    right: &objects::StringLit,
) -> Result<objects::Object> {
    match ope {
        ast::Operator::Plus => {
            let mut value = left.value.clone();
            value.push_str(&right.value);
            Ok(objects::StringLit { value }.into())
        }
        unknown => new_error(&format!("unknown operator: String {} String", unknown)),
    }
}

fn eval_if_expr(if_expr: &ast::If, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
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

fn is_truthy(obj: objects::Object) -> bool {
    match obj {
        objects::Object::Null(_) => false,
        objects::Object::Boolean(b) => match b {
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
) -> Result<objects::Object> {
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
) -> Result<Vec<objects::Object>> {
    let mut result = Vec::<objects::Object>::new();

    for expr in expr_list.iter() {
        result.push(eval_expr(expr, Rc::clone(&env))?);
    }

    Ok(result)
}

fn apply_function(func: &objects::Object, args: &[objects::Object]) -> Result<objects::Object> {
    match func {
        objects::Object::Function(f) => {
            let extended_env = extend_function_env(f, args)?;
            let evaluated = eval_stmt(&f.body.clone().into(), extended_env)?;
            Ok(unwrap_return_value(&evaluated))
        }
        objects::Object::Builtin(builtin) => Ok(match builtin.call(args)? {
            Some(res) => res,
            None => NULL.into(),
        }),
        invalid => new_error(&format!("not a function: {}", invalid.o_type())),
    }
}

fn extend_function_env(
    func: &objects::Function,
    args: &[objects::Object],
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

fn unwrap_return_value(obj: &objects::Object) -> objects::Object {
    match obj.clone() {
        objects::Object::Return(o) => *o.value,
        o => o,
    }
}

fn eval_index_expr<'a>(
    left: &'a objects::Object,
    index: &objects::Object,
) -> Result<&'a objects::Object> {
    match (left, index) {
        (objects::Object::Array(l), objects::Object::Integer(idx)) => {
            Ok(eval_array_index_expr(l, idx)?)
        }
        (objects::Object::Hash(l), idx) => Ok(eval_hash_index_expr(l, idx)?),
        (l, _) => new_error(&format!("index operator not supported: {}", l.o_type()))?,
    }
}

fn eval_array_index_expr<'a>(
    array: &'a objects::Array,
    index: &objects::Integer,
) -> Result<&'a objects::Object> {
    if index.value < 0 {
        return Ok(&objects::Object::Null(NULL));
    }
    let idx = usize::try_from(index.value).or_else(|e| new_error(&e.to_string()))?;

    match array.elements.get(idx) {
        Some(obj) => Ok(obj),
        None => Ok(&objects::Object::Null(NULL)),
    }
}

fn eval_hash_literal(node: &ast::Hash, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    let mut pairs = objects::HashPairs::new();

    for pair in node.pairs.iter() {
        let key = eval_expr(&pair.key, Rc::clone(&env))?;
        let value = eval_expr(&pair.value, Rc::clone(&env))?;
        let key_type = key.o_type();

        match objects::HashableObject::try_from(key) {
            Ok(o) => pairs.insert(o, value),
            Err(_) => new_error(&format!("unusable as hash key: {}", key_type))?,
        };
    }

    Ok(objects::Hash { pairs }.into())
}

fn eval_hash_index_expr<'a>(
    hash: &'a objects::Hash,
    key: &objects::Object,
) -> Result<&'a objects::Object> {
    let key_type = key.o_type();
    match objects::HashableObject::try_from(key.clone()) {
        Ok(o) => Ok(match hash.pairs.get(&o) {
            Some(value) => value,
            None => &objects::Object::Null(NULL),
        }),
        Err(_) => new_error(&format!("unusable as hash key: {}", key_type))?,
    }
}

fn quote(node: ast::Node, env: Rc<RefCell<Environment>>) -> Result<objects::Object> {
    let node = eval_unquote_calls(node, env)?;
    Ok(objects::Quote { node }.into())
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

fn convert_object_to_ast_node(obj: objects::Object) -> ast::Node {
    match obj {
        objects::Object::Integer(int) => ast::Expr::from(ast::Integer { value: int.value }).into(),
        objects::Object::Boolean(b) => ast::Expr::from(ast::Boolean { value: b.value }).into(),
        objects::Object::Quote(q) => q.node,
        _ => unimplemented!(),
    }
}

fn is_unquote_call(node: &ast::Node) -> bool {
    match node {
        ast::Node::Expr(ast::Expr::Call(call)) => (*call.func).to_string() == "unquote",
        _ => false,
    }
}

pub fn define_macros(program: &mut ast::Program, env: Rc<RefCell<Environment>>) -> Result<()> {
    program
        .statements
        .iter()
        .filter(|stmt| is_macro_definition(stmt))
        .try_for_each(|stmt| add_macro(stmt, Rc::clone(&env)))?;

    program.statements = program
        .statements
        .clone()
        .into_iter()
        .filter(|stmt| !is_macro_definition(stmt))
        .collect::<Vec<ast::Stmt>>();

    Ok(())
}

fn is_macro_definition(stmt: &ast::Stmt) -> bool {
    matches!(
        stmt,
        ast::Stmt::Let(ast::Let {
            value: ast::Expr::MacroLit(_),
            ..
        })
    )
}

fn add_macro(stmt: &ast::Stmt, env: Rc<RefCell<Environment>>) -> Result<()> {
    let let_stmt = match stmt {
        ast::Stmt::Let(l) => l,
        stmt => return Err(anyhow::format_err!("expect Let. received {}", stmt)),
    };
    let ast::Let { name, value } = let_stmt;

    let m_macro = match value {
        ast::Expr::MacroLit(m) => m,
        stmt => return Err(anyhow::format_err!("expect Macro. received {}", stmt)),
    };
    let ast::MacroLit { params, body, .. } = m_macro;

    let m_macro = objects::Macro {
        params: params.clone(),
        body: body.clone(),
        env: Rc::clone(&env),
    };

    env.borrow_mut().insert(&name.to_string(), m_macro.into());

    Ok(())
}

pub fn expand_macros(program: ast::Node, env: Rc<RefCell<Environment>>) -> Result<ast::Node> {
    tools::modify(program, |node| {
        let call = match &node {
            ast::Node::Expr(ast::Expr::Call(call)) => call,
            _ => return Ok(node),
        };

        let m_macro = get_macro_in_env(call, Rc::clone(&env));
        let m_macro = if let Some(m) = m_macro {
            m
        } else {
            return Ok(node);
        };

        let args = quote_args(call.clone());
        let eval_env = extend_macro_env(m_macro.clone(), args);

        let evaluated = eval_stmt(&m_macro.body.into(), Rc::new(RefCell::new(eval_env)))?;

        let quote = match evaluated {
            objects::Object::Quote(q) => q,
            o => {
                return Err(anyhow::format_err!(
                    "we only support returning AST-nodes from macros. {}",
                    o
                ))
            }
        };

        Ok(quote.node)
    })
}

fn get_macro_in_env(call: &ast::Call, env: Rc<RefCell<Environment>>) -> Option<objects::Macro> {
    let ident = match &(*call.func) {
        ast::Expr::Identifier(id) => id,
        _ => return None,
    };

    let obj = env.borrow().get(&ident.value)?;
    match obj {
        objects::Object::Macro(m) => Some(m),
        _ => None,
    }
}

fn quote_args(call: ast::Call) -> Vec<objects::Quote> {
    call.args
        .into_iter()
        .map(|arg| objects::Quote { node: arg.into() })
        .collect::<Vec<objects::Quote>>()
}

fn extend_macro_env(m_macro: objects::Macro, args: Vec<objects::Quote>) -> Environment {
    let mut extended = Environment::new(Some(Rc::clone(&m_macro.env)));

    m_macro
        .params
        .into_iter()
        .zip(args)
        .for_each(|(id, quote)| {
            extended.insert(&id.value, quote.into());
        });

    extended
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
                    objects::Object::Function(o) => {
                        assert_eq!(o.params.len(), expected_params_size);
                        assert_eq!(o.params[0].to_string(), expected_params);
                        assert_eq!(o.body.to_string(), expected_body);
                    }
                    o => panic!("expected Function. received {}", o),
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
        tests
            .into_iter()
            .for_each(|(input, expected)| assert_integer_array_object(eval(input), expected));

        let input = "push([1, 2, 3], [4, 5])";
        let expected1 = 1_i64;
        let expected2 = 2_i64;
        let expected3 = 3_i64;
        let expected4 = vec![4_i64, 5_i64];
        let evaluated = eval(input);
        match evaluated {
            objects::Object::Array(o) => {
                assert_eq!(o.elements.len(), 4);
                assert_integer_object(o.elements[0].clone(), expected1);
                assert_integer_object(o.elements[1].clone(), expected2);
                assert_integer_object(o.elements[2].clone(), expected3);
                assert_integer_array_object(o.elements[3].clone(), expected4)
            }
            o => panic!("expected Array, received {:?}.", o),
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
            objects::Object::Hash(evaluated) => {
                assert_eq!(evaluated.pairs.len(), 6);

                let expected = vec![
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::StringLit {
                                value: "one".into(),
                            },
                        ))
                        .unwrap(),
                        1_i64,
                    ),
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::StringLit {
                                value: "two".into(),
                            },
                        ))
                        .unwrap(),
                        2_i64,
                    ),
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::StringLit {
                                value: "three".into(),
                            },
                        ))
                        .unwrap(),
                        3_i64,
                    ),
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::Integer { value: 4_i64 },
                        ))
                        .unwrap(),
                        4_i64,
                    ),
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::Boolean { value: true },
                        ))
                        .unwrap(),
                        5_i64,
                    ),
                    (
                        objects::HashableObject::try_from(objects::Object::from(
                            objects::Boolean { value: false },
                        ))
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
            o => panic!("expected Hash. received {:?}", o),
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
                objects::Object::Quote(o) => assert_eq!(o.to_string(), expected),
                o => panic!("expected Quote. received {:?}", o),
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
                objects::Object::Quote(o) => assert_eq!(o.to_string(), expected),
                o => panic!("expected Quote. received {:?}", o),
            }
        });
    }

    #[test]
    fn test_define_macro() {
        let input = "
            let number = 1;
            let function = fn(x, y) { x + y; };
            let mymacro = macro(x, y) { x + y; };
        ";

        let env = Rc::new(RefCell::new(Environment::new(None)));
        let mut program = {
            let l = crate::lexer::Lexer::new(input.into());
            let mut p = crate::parser::Parser::new(l);
            p.parse_program().unwrap()
        };

        define_macros(&mut program, Rc::clone(&env)).unwrap();

        assert_eq!(program.statements.len(), 2);

        assert!(env.borrow().get("number").is_none());
        assert!(env.borrow().get("function").is_none());

        let obj = env.borrow().get("mymacro");
        assert!(obj.is_some());

        let m_macro = match obj.unwrap() {
            objects::Object::Macro(m) => m,
            obj => panic!("expect Macro. received {}", obj),
        };

        assert_eq!(m_macro.params.len(), 2);
        assert_eq!(m_macro.params[0].to_string(), "x");
        assert_eq!(m_macro.params[1].to_string(), "y");

        let expected_body = "{ (x + y) }";
        assert_eq!(m_macro.body.to_string(), expected_body);
    }

    #[test]
    fn test_expand_macros() {
        let tests = vec![
            (
                "
                    let infix_expr = macro() { quote(1 + 2) };
                    infix_expr();
                ",
                "(1 + 2)",
            ),
            (
                "
                    let reverse = macro(a, b) { quote(unquote(b) - unquote(a)); };
                    reverse(2 + 2, 10 - 5);
                ",
                "(10 - 5) - (2 + 2)",
            ),
            (
                r#"
                    let unless = macro(condition, consequence, alternative) {
                        quote(
                            if (!(unquote(condition))) {
                                unquote(consequence);
                            } else {
                                unquote(alternative);
                            }
                        );
                    };

                    unless(10 > 5, puts("not greater"), puts("greater"));
                "#,
                r#"if (!(10 > 5)) { puts("not greater") } else { puts("greater") }"#,
            ),
        ];

        tests.into_iter().for_each(|(input, expected)| {
            let expected = {
                let l = crate::lexer::Lexer::new(expected.into());
                let mut p = crate::parser::Parser::new(l);
                p.parse_program().unwrap()
            };

            let mut program = {
                let l = crate::lexer::Lexer::new(input.into());
                let mut p = crate::parser::Parser::new(l);
                p.parse_program().unwrap()
            };
            let env = Rc::new(RefCell::new(Environment::new(None)));
            define_macros(&mut program, Rc::clone(&env)).unwrap();

            let expanded = expand_macros(program.into(), Rc::clone(&env)).unwrap();

            assert_eq!(expanded.to_string(), expected.to_string());
            assert_eq!(expanded, expected.into());
        });
    }

    #[test]
    fn test_fibonacci() {
        let input = "
            let fibonacci = fn(x) {
                if (x == 0) {
                    return 0;
                } else {
                    if (x == 1) {
                        return 1;
                    } else {
                        fibonacci(x - 1) + fibonacci(x - 2);
                    }
                }
            };
            fibonacci(15);
        ";

        let env = Rc::new(RefCell::new(Environment::new(None)));
        let program = {
            let l = crate::lexer::Lexer::new(input.into());
            let mut p = crate::parser::Parser::new(l);
            p.parse_program().unwrap()
        };

        let obj = eval_node(&program.into(), env).unwrap();
        match obj {
            objects::Object::Integer(i) => assert_eq!(i.value, 610),
            other => panic!("expected Integer. received {}", other),
        };
    }

    fn check_err_and_unrwap<T, E>(result: std::result::Result<T, E>, input: &str) -> T
    where
        E: std::fmt::Debug,
    {
        result
            .map_err(move |e| format!("{} //=> {:?}", input, e))
            .unwrap()
    }

    fn eval(input: &str) -> objects::Object {
        let evaluated = eval_non_check(input);
        check_err_and_unrwap(evaluated, input)
    }

    fn eval_non_check(input: &str) -> Result<objects::Object> {
        let l = crate::lexer::Lexer::new(input.to_string());
        let mut p = crate::parser::Parser::new(l);

        let program = p.parse_program();
        let program = check_err_and_unrwap(program, input);

        let env = Rc::new(RefCell::new(Environment::new(None)));
        eval_program(&program, env)
    }

    fn assert_integer_object(obj: objects::Object, expected: i64) {
        match obj {
            objects::Object::Integer(o) => assert_eq!(o.value, expected),
            o => panic!("expected Integer. received {:?}", o),
        }
    }

    fn assert_boolean_object(obj: objects::Object, expected: bool) {
        match obj {
            objects::Object::Boolean(o) => assert_eq!(o.value, expected),
            o => panic!("expected Boolean. received {:?}", o),
        }
    }

    fn assert_null_object(obj: objects::Object) {
        match obj {
            objects::Object::Null(_) => (),
            o => panic!("expected Null. received {:?}", o),
        }
    }

    fn assert_error_object(err: anyhow::Error, expected: &str) {
        assert_eq!(err.to_string(), expected)
    }

    fn assert_string_object(obj: objects::Object, expected: &str) {
        match obj {
            objects::Object::StringLit(o) => assert_eq!(o.value, expected),
            o => panic!("expected StringLit. received {:?}", o),
        }
    }

    fn assert_integer_array_object(obj: objects::Object, expected_arr: Vec<i64>) {
        match obj {
            objects::Object::Array(o) => {
                assert_eq!(o.elements.len(), expected_arr.len());

                expected_arr
                    .into_iter()
                    .zip(o.elements)
                    .for_each(|(expected, ele)| match ele {
                        objects::Object::Integer(o) => assert_eq!(o.value, expected),
                        o => panic!("expected Array<Integer>. received {:?}", o),
                    })
            }
            o => panic!("expected Array<Integer>. received {:?}", o),
        }
    }

    fn assert_string_array_object(obj: objects::Object, expected_arr: Vec<&str>) {
        match obj {
            objects::Object::Array(o) => {
                assert_eq!(o.elements.len(), expected_arr.len());

                expected_arr
                    .into_iter()
                    .zip(o.elements)
                    .for_each(|(expected, ele)| match ele {
                        objects::Object::StringLit(o) => assert_eq!(o.value, expected),
                        o => panic!("expected Array<Integer>. received {:?}", o),
                    })
            }
            o => panic!("expected Array<Integer>. received {:?}", o),
        }
    }
}
