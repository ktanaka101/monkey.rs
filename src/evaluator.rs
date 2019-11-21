use crate::ast;
use crate::builtin::BuiltinFunction;
use crate::env::Environment;
use crate::object;
use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;
use std::result;

pub const TRUE: object::Boolean = object::Boolean { value: true };
pub const FALSE: object::Boolean = object::Boolean { value: false };
pub const NULL: object::Null = object::Null {};

type Result<T> = result::Result<T, object::Error>;

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
    Err(object::Error {
        message: message.to_string(),
    })
}

fn eval_program(program: &ast::Program, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let mut result = None;
    for stmt in program.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            object::Object::Return(r) => return Ok(r.value.as_ref().clone()),
            o => result = Some(o),
        }
    }

    match result {
        Some(r) => Ok(r),
        _ => new_error(&format!("program statements empty: {}", program)),
    }
}

fn eval_block(block: &ast::Block, env: Rc<RefCell<Environment>>) -> Result<object::Object> {
    let mut result = None;
    for stmt in block.statements.iter() {
        match eval_stmt(stmt, Rc::clone(&env))? {
            object::Object::Return(r) => return Ok(r.into()),
            o => result = Some(o),
        }
    }

    match result {
        Some(r) => Ok(r),
        _ => new_error(&format!("program statements empty: {}", block)),
    }
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
        (ast::Operator::NotEqual, l, r) => Ok(native_bool_to_boolean_object(l == r)),
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
    use crate::ast::Operator::*;
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
        unknown => new_error(&format!("unknown operator: {} {} {}", unknown, left, right)),
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

    let builtin = BuiltinFunction::from_str(&node.value);
    if let Some(builtin) = builtin {
        return Ok(builtin.to_object());
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

        match key.try_into_hashable_object() {
            Some(o) => pairs.insert(o, value),
            None => new_error(&format!("unusable as hash key: {}", key_type))?,
        };
    }

    Ok(object::Hash { pairs }.into())
}

fn eval_hash_index_expr<'a>(
    hash: &'a object::Hash,
    key: &object::Object,
) -> Result<&'a object::Object> {
    let key_type = key.o_type();
    match key.clone().try_into_hashable_object() {
        Some(o) => Ok(match hash.pairs.get(&o) {
            Some(value) => &value,
            None => &object::Object::Null(NULL),
        }),
        None => new_error(&format!("unusable as hash key: {}", key_type))?,
    }
}
