use std::convert::{TryFrom, TryInto};

use anyhow::Result;

use super::ast::{Expr, Identifier, Node, Pair, Stmt};

pub fn modify<F>(node: Node, modifier: F) -> Result<Node>
where
    F: Fn(Node) -> Result<Node> + Copy,
{
    let node: Node = match node {
        Node::Program(mut program) => {
            program.statements = program
                .statements
                .into_iter()
                .map(|stmt| modify(stmt.into(), modifier))
                .map(|node| Stmt::try_from(node?))
                .collect::<Result<Vec<Stmt>>>()?;

            program.into()
        }
        Node::Stmt(stmt) => match stmt {
            Stmt::ExprStmt(expr_stmt) => modify(expr_stmt.expr.into(), modifier)?,
            Stmt::Block(mut block) => {
                block.statements = block
                    .statements
                    .into_iter()
                    .map(|stmt| modify(stmt.into(), modifier)?.try_into())
                    .collect::<Result<Vec<Stmt>>>()?;

                Stmt::from(block).into()
            }
            Stmt::Return(mut mreturn) => {
                mreturn.return_value = modify(mreturn.return_value.into(), modifier)?.try_into()?;

                Stmt::from(mreturn).into()
            }
            Stmt::Let(mut mlet) => {
                mlet.value = modify(mlet.value.into(), modifier)?.try_into()?;

                Stmt::from(mlet).into()
            }
        },
        Node::Expr(expr) => match expr {
            Expr::InfixExpr(mut infix_expr) => {
                let left = modify((*infix_expr.left).into(), modifier)?;
                infix_expr.left = Box::new(left.try_into()?);

                let right = modify((*infix_expr.right).into(), modifier)?;
                infix_expr.right = Box::new(right.try_into()?);

                Expr::from(infix_expr).into()
            }
            Expr::PrefixExpr(mut prefix_expr) => {
                let right = modify((*prefix_expr.right).into(), modifier)?;
                prefix_expr.right = Box::new(right.try_into()?);

                Expr::from(prefix_expr).into()
            }
            Expr::Index(mut idx) => {
                let left = modify((*idx.left).into(), modifier)?;
                idx.left = Box::new(left.try_into()?);

                let inner_idx = modify((*idx.index).into(), modifier)?;
                idx.index = Box::new(inner_idx.try_into()?);

                Expr::from(idx).into()
            }
            Expr::If(mut if_expr) => {
                let cond = modify((*if_expr.cond).into(), modifier)?;
                if_expr.cond = Box::new(cond.try_into()?);

                let block = modify(Stmt::from(if_expr.consequence).into(), modifier)?;
                if_expr.consequence = Stmt::try_from(block)?.try_into()?;

                if let Some(block) = if_expr.alternative {
                    let block = modify(Stmt::from(block).into(), modifier)?;
                    if_expr.alternative = Some(Stmt::try_from(block)?.try_into()?);
                }

                Expr::from(if_expr).into()
            }
            Expr::Function(mut func) => {
                func.params = func
                    .params
                    .into_iter()
                    .map(|param| {
                        Expr::try_from(modify(Expr::from(param).into(), modifier)?)?
                            .try_into()
                    })
                    .collect::<Result<Vec<Identifier>>>()?;

                func.body =
                    Stmt::try_from(modify(Stmt::from(func.body).into(), modifier)?)?.try_into()?;

                Expr::from(func).into()
            }
            Expr::Array(mut arr) => {
                arr.elements = arr
                    .elements
                    .into_iter()
                    .map(|expr| modify(expr.into(), modifier)?.try_into())
                    .collect::<Result<Vec<Expr>>>()?;

                Expr::from(arr).into()
            }
            Expr::Hash(mut hs) => {
                hs.pairs = hs
                    .pairs
                    .into_iter()
                    .map(|mut pair| {
                        let key = Expr::try_from(modify(pair.key.into(), modifier)?)?;
                        let value = Expr::try_from(modify(pair.value.into(), modifier)?)?;

                        pair.key = key;
                        pair.value = value;
                        Ok(pair)
                    })
                    .collect::<Result<Vec<Pair>>>()?;

                Expr::from(hs).into()
            }
            expr => expr.into(),
        },
    };

    modifier(node)
}

#[cfg(test)]
mod tests {
    use super::super::ast::*;
    use super::*;

    #[test]
    fn test_modify() {
        let one = || Expr::from(Integer { value: 1 });
        let two = || Expr::from(Integer { value: 2 });

        fn turn_one_into_two(node: Node) -> Result<Node> {
            match node {
                Node::Stmt(Stmt::ExprStmt(expr_stmt)) => turn_one_into_two(expr_stmt.expr.into()),
                Node::Expr(Expr::Integer(mut int)) => {
                    if int.value != 1 {
                        return Ok(Expr::from(int).into());
                    }

                    int.value = 2;
                    Ok(Expr::from(int).into())
                }
                expr => Ok(expr),
            }
        }

        let tests: Vec<(Node, Node)> = vec![
            (one().into(), two().into()),
            (
                Program {
                    statements: vec![Stmt::ExprStmt(ExprStmt { expr: one() })],
                }
                .into(),
                Program {
                    statements: vec![Stmt::ExprStmt(ExprStmt { expr: two() })],
                }
                .into(),
            ),
            (
                Expr::from(InfixExpr {
                    left: one().into(),
                    ope: Operator::Plus,
                    right: two().into(),
                })
                .into(),
                Expr::from(InfixExpr {
                    left: two().into(),
                    ope: Operator::Plus,
                    right: two().into(),
                })
                .into(),
            ),
            (
                Expr::from(InfixExpr {
                    left: two().into(),
                    ope: Operator::Plus,
                    right: one().into(),
                })
                .into(),
                Expr::from(InfixExpr {
                    left: two().into(),
                    ope: Operator::Plus,
                    right: two().into(),
                })
                .into(),
            ),
            (
                Expr::from(PrefixExpr {
                    ope: Operator::Plus,
                    right: one().into(),
                })
                .into(),
                Expr::from(PrefixExpr {
                    ope: Operator::Plus,
                    right: two().into(),
                })
                .into(),
            ),
            (
                Expr::from(Index {
                    left: one().into(),
                    index: one().into(),
                })
                .into(),
                Expr::from(Index {
                    left: two().into(),
                    index: two().into(),
                })
                .into(),
            ),
            (
                Expr::from(If {
                    cond: one().into(),
                    consequence: Block {
                        statements: vec![ExprStmt { expr: one() }.into()],
                    },
                    alternative: Some(Block {
                        statements: vec![ExprStmt { expr: one() }.into()],
                    }),
                })
                .into(),
                Expr::from(If {
                    cond: two().into(),
                    consequence: Block {
                        statements: vec![ExprStmt { expr: two() }.into()],
                    },
                    alternative: Some(Block {
                        statements: vec![ExprStmt { expr: two() }.into()],
                    }),
                })
                .into(),
            ),
            (
                Stmt::from(Return {
                    return_value: one(),
                })
                .into(),
                Stmt::from(Return {
                    return_value: two(),
                })
                .into(),
            ),
            (
                Stmt::from(Let {
                    name: Identifier { value: "x".into() },
                    value: one(),
                })
                .into(),
                Stmt::from(Let {
                    name: Identifier { value: "x".into() },
                    value: two(),
                })
                .into(),
            ),
            (
                Expr::from(Function {
                    params: Vec::<Identifier>::new(),
                    body: Block {
                        statements: vec![ExprStmt { expr: one() }.into()],
                    },
                    name: "".to_string(),
                })
                .into(),
                Expr::from(Function {
                    params: Vec::<Identifier>::new(),
                    body: Block {
                        statements: vec![ExprStmt { expr: two() }.into()],
                    },
                    name: "".to_string(),
                })
                .into(),
            ),
            (
                Expr::from(Array {
                    elements: vec![one()],
                })
                .into(),
                Expr::from(Array {
                    elements: vec![two()],
                })
                .into(),
            ),
            (
                Expr::from(Hash {
                    pairs: vec![Pair {
                        key: one(),
                        value: one(),
                    }],
                })
                .into(),
                Expr::from(Hash {
                    pairs: vec![Pair {
                        key: two(),
                        value: two(),
                    }],
                })
                .into(),
            ),
        ];

        tests.into_iter().for_each(|(input, expected)| {
            let modified = modify(input, turn_one_into_two);
            assert_eq!(modified.unwrap().to_string(), expected.to_string());
        });
    }
}
