use std::collections::{HashMap, HashSet, VecDeque};
use std::error::Error;
use syn::{
    Expr, Field, File, GenericArgument, Item, ItemFn, Member, Pat, Path, PathArguments, Stmt,
    Stmt::Local, Type, TypePath, parse_str,
};
use thiserror::Error;

#[derive(Debug)]
struct AnalysisResult {
    message: String,
}

#[derive(Error, Debug)]
enum AnalysisError {
    #[error("unimplemented")]
    ToDo,
}

fn is_struct_creation(expr_repr: ExprRepr) -> Option<String> {
    if let ExprRepr::CallRepr { func: func_rc, arg } = expr_repr {
        if let ExprRepr::CallRepr {
            func: func_ref_cell,
            arg: arg_struct_name,
        } = *arg
        {
            if let ExprRepr::StructRepr(name) = *arg_struct_name {
                return Some(name);
            }
        }
    }
    None
}

fn is_borrow(expr_repr: ExprRepr) -> Option<(String, bool)> {
    if let ExprRepr::MethodCallRepr { base, method } = expr_repr {
        if let ExprRepr::PathRepr(path) = *base {
            if let Some(last) = path.last() {
                if method == "borrow" {
                    return Some((last.clone(), false));
                } else if method == "borrow_mut" {
                    return Some((last.clone(), true));
                }
            }
        }
    }
    None
}

fn reachable_from_main(
    q_var: String,
    map: &mut StructMap,
    vars_in_main: &mut HashSet<String>,
) -> bool {
    let mut visited = HashSet::new();

    for var in vars_in_main.iter() {
        if search(var, &q_var, &mut visited, map) {
            return true;
        }
    }

    false
}

fn reachable_from_self(q_var: String, map: &mut StructMap) -> bool {
    if let Some(target) = map.get(&q_var) {
        let mut visited = HashSet::new();

        for var in target.refs.iter() {
            if search(var.1, &q_var, &mut visited, map) {
                return true;
            }
        }
    }

    false
}

fn search(from: &String, for_var: &String, visited: &mut HashSet<String>, map: &StructMap) -> bool {
    if *from == *for_var {
        return true;
    }
    if visited.contains(from) {
        return false;
    }
    if let Some(curr) = map.get(from) {
        visited.insert(from.clone());
        for referen in curr.refs.iter() {
            if search(referen.1, for_var, visited, map) {
                return true;
            }
        }
    }
    false
}

fn borrow_ok(map: &mut StructMap, borrowed_var: &String, is_mutable: bool) -> bool {
    match map.get(borrowed_var) {
        Some(key_struct) => {
            let mut new_struct = key_struct.clone();
            if is_mutable {
                if key_struct.active_mut_borrow {
                    false
                } else if key_struct.active_borrows > 0 {
                    new_struct.active_mut_borrow = true;
                    map.insert(borrowed_var.clone(), new_struct);
                    false
                } else {
                    new_struct.active_mut_borrow = true;
                    map.insert(borrowed_var.clone(), new_struct);
                    true
                }
            } else {
                new_struct.active_borrows += 1;
                let res = !key_struct.active_mut_borrow;
                map.insert(borrowed_var.clone(), new_struct);
                res
            }
        }

        None => false,
    }
}

fn analyze_stmt(
    stmt: Stmt,
    catalog: &StructMapAbstract,
    map: &mut StructMap,
    vars_in_main: &mut HashSet<String>,
    borrow_vars: &mut HashMap<String, (String, bool)>,
) -> Option<Result<AnalysisResult, AnalysisError>> {
    match stmt {
        Local(local) => match (local.pat, local.init) {
            (Pat::Ident(pat_ident), Some(local_init)) => {
                let full_path = get_full(*local_init.expr);
                if let Some(name) = is_struct_creation(full_path.clone()) {
                    map.insert(
                        pat_ident.ident.to_string(),
                        StructRepr {
                            name,
                            refs: HashMap::new(),
                            active_borrows: 0,
                            active_mut_borrow: false,
                        },
                    );

                    vars_in_main.insert(pat_ident.ident.to_string());
                } else if let Some((borrowed_var, is_mutable)) = is_borrow(full_path) {
                    borrow_vars.insert(
                        pat_ident.ident.to_string(),
                        (borrowed_var.clone(), is_mutable),
                    );

                    if !borrow_ok(map, &borrowed_var, is_mutable) {
                        return Some(Ok(AnalysisResult {
                            message: format!(
                                "borrowing {borrowed_var} failed because of an invalid borrow configuration"
                            ),
                        }));
                    }
                }
                None
            }
            _ => Some(Err(AnalysisError::ToDo)),
        },
        Stmt::Expr(expr, _) => {
            let transformed = get_full(expr);

            #[allow(clippy::single_match)]
            match transformed {
                ExprRepr::AssignRepr { left, right } => {
                    #[allow(clippy::collapsible_if)]
                    if let ExprRepr::FieldRepr { base, member } = *left {
                        if let ExprRepr::MethodCallRepr { base, method } = *base {
                            if let ExprRepr::PathRepr(path) = *base {
                                let left_side_var_name = path[0].clone();

                                if let ExprRepr::CallRepr { func, arg } = *right {
                                    if let ExprRepr::MethodCallRepr { base, method } = *arg {
                                        if let ExprRepr::PathRepr(path_right) = *base {
                                            let left_side_repr = map.get(&left_side_var_name)?;
                                            let right_side_var_name = path_right[0].clone();
                                            let mut new_refs = left_side_repr.refs.clone();
                                            new_refs.insert(member, right_side_var_name);
                                            map.insert(
                                                left_side_var_name,
                                                StructRepr {
                                                    name: left_side_repr.name.clone(),
                                                    refs: new_refs,
                                                    active_borrows: left_side_repr.active_borrows,
                                                    active_mut_borrow: left_side_repr
                                                        .active_mut_borrow,
                                                },
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                ExprRepr::CallRepr { func, arg } => {
                    if let (ExprRepr::PathRepr(func_path), ExprRepr::PathRepr(arg_path)) =
                        (*func, *arg)
                    {
                        let func = func_path[0].clone();
                        let arg = arg_path[0].clone();

                        if func == "drop" && vars_in_main.remove(&arg) {
                            let reachable_from_main =
                                reachable_from_main(arg.clone(), map, vars_in_main);
                            let reachable_from_self = reachable_from_self(arg.clone(), map);
                            if (!reachable_from_main && reachable_from_self) {
                                return Some(Ok(AnalysisResult {
                                    message: format!(
                                        "dropping {arg} leaked memory as b still has remaining references"
                                    ),
                                }));
                            }
                        }
                    }
                }
                expr => {
                    println!("{:?}", expr);
                }
            }
            None
        }
        _ => None,
    }
}

fn analyze_fn(
    item_fn: ItemFn,
    catalog: &StructMapAbstract,
) -> Result<Vec<AnalysisResult>, AnalysisError> {
    let mut map = StructMap::new();
    let mut results = Vec::new();
    let mut vars_in_main = HashSet::new();
    let mut borrow_vars = HashMap::new();

    for stmt in item_fn.block.stmts {
        let res = analyze_stmt(stmt, catalog, &mut map, &mut vars_in_main, &mut borrow_vars);
        if let Some(result) = res {
            let unwrapped_result = result?;
            results.push(unwrapped_result);
        }
    }

    Ok(results)
}

#[derive(Debug)]
struct StructReprAbstract {
    name: String,
    refs: HashMap<String, String>,
}

#[derive(Debug, Clone)]
struct StructRepr {
    name: String,
    refs: HashMap<String, String>,
    active_borrows: u32,
    active_mut_borrow: bool,
}

type StructMap = HashMap<String, StructRepr>;
type StructMapAbstract = HashMap<String, StructReprAbstract>;

fn get_generic_chain(ty: Type) -> VecDeque<String> {
    match ty {
        Type::Path(type_path) => get_generic_chain_helper(type_path),
        _ => VecDeque::new(),
    }
}

fn get_generic_chain_helper(type_path: TypePath) -> VecDeque<String> {
    if let Some(final_segment) = type_path.path.segments.last() {
        let final_name = final_segment.ident.to_string();

        let mut remainder = VecDeque::new();
        #[allow(clippy::collapsible_if)]
        if let PathArguments::AngleBracketed(outer_args) = &final_segment.arguments {
            if let Some(GenericArgument::Type(Type::Path(middle_path))) = outer_args.args.first() {
                remainder = get_generic_chain_helper(middle_path.clone());
            }
        }
        remainder.push_front(final_name);
        remainder
    } else {
        VecDeque::new()
    }
}

fn get_call_path(path: Path) -> Vec<String> {
    let mut path_vec = Vec::new();

    for segment in path.segments.iter() {
        let name = segment.ident.to_string();
        path_vec.push(name);
    }

    path_vec
}

fn get_last_segment_name(path: Path) -> String {
    match path.segments.last() {
        Some(final_segment) => final_segment.ident.to_string(),
        None => String::new(),
    }
}

fn member_to_string(member: Member) -> String {
    match member {
        Member::Named(named) => named.to_string(),
        Member::Unnamed(unnamed) => unnamed.index.to_string(),
    }
}

#[derive(Debug, Clone)]
enum ExprRepr {
    AssignRepr {
        left: Box<ExprRepr>,
        right: Box<ExprRepr>,
    },
    StructRepr(String),
    FieldRepr {
        base: Box<ExprRepr>,
        member: String,
    },
    MethodCallRepr {
        base: Box<ExprRepr>,
        method: String,
    },
    PathRepr(Vec<String>),
    CallRepr {
        func: Box<ExprRepr>,
        arg: Box<ExprRepr>,
    },
}

fn get_full(expr: Expr) -> ExprRepr {
    match expr {
        Expr::Call(expr_call) => match expr_call.args.first() {
            Some(next) => ExprRepr::CallRepr {
                func: Box::new(get_full(*expr_call.func.clone())),
                arg: Box::new(get_full(next.clone())),
            },
            None => {
                panic!("expr call without argument");
            }
        },
        Expr::Path(expr_path) => ExprRepr::PathRepr(get_call_path(expr_path.path)),
        Expr::Struct(expr_struct) => ExprRepr::StructRepr(get_last_segment_name(expr_struct.path)),
        Expr::Assign(expr_assign) => ExprRepr::AssignRepr {
            left: Box::new(get_full(*expr_assign.left)),
            right: Box::new(get_full(*expr_assign.right)),
        },
        Expr::Field(expr_field) => ExprRepr::FieldRepr {
            base: Box::new(get_full(*expr_field.base)),
            member: member_to_string(expr_field.member),
        },
        Expr::MethodCall(method_call) => ExprRepr::MethodCallRepr {
            base: Box::new(get_full(*method_call.receiver)),
            method: method_call.method.to_string(),
        },
        _ => panic!("Unhandled expr"),
    }
}

fn field_comprehender(field: Field, names: &[String]) -> Option<(String, String)> {
    let field_name = field.ident?.to_string();
    let mut generic_chain = get_generic_chain(field.ty.clone());

    let struct_to = generic_chain.pop_back()?;

    if !names.contains(&struct_to) {
        return None;
    }

    Some((field_name, struct_to))
}

fn catalog_structs(file: File) -> StructMapAbstract {
    let mut names: Vec<String> = Vec::new();
    let mut structs: StructMapAbstract = HashMap::new();

    for item in file.items.iter() {
        if let Item::Struct(item_struct) = item {
            names.push(item_struct.ident.to_string())
        }
    }

    for item in file.items.iter() {
        if let Item::Struct(item_struct) = item {
            let mut struct_repr = StructReprAbstract {
                name: item_struct.ident.to_string(),
                refs: HashMap::new(),
            };

            for field in item_struct.fields.iter() {
                if let Some(comprehended) = field_comprehender(field.clone(), &names) {
                    struct_repr.refs.insert(comprehended.0, comprehended.1);
                }
            }

            structs.insert(item_struct.ident.to_string(), struct_repr);
        }
    }

    structs
}

fn analyze_file(file: File) -> Result<Vec<AnalysisResult>, AnalysisError> {
    let mut results = Vec::new();

    let structs = catalog_structs(file.clone());

    for item in file.items {
        if let Item::Fn(item_fn) = item {
            let mut result = analyze_fn(item_fn, &structs)?;
            results.append(&mut result);
        }
    }

    Ok(results)
}

fn main() -> Result<(), Box<dyn Error>> {
    let source_code = r#"
    use std::rc::Rc;
    use std::cell::RefCell;

    struct Node {
        id: i32,
        next: Option<Rc<RefCell<Node>>>,
    }

    impl Drop for Node {
        fn drop(&mut self) {
            println!("Node {} dropped.", self.id);
        }
    }

    fn main() {
        let a = Rc::new(RefCell::new(Node { id: 1, next: None }));

        let b = Rc::new(RefCell::new(Node {
            id: 2,
            next: Some(a.clone())
        }));

        a.borrow_mut().next = Some(b.clone());
        b.borrow_mut().next = Some(a.clone());

        let c = a.borrow();
        let d = a.borrow_mut();

        drop(a);
        drop(b);
    }
    "#;

    let ast: File = parse_str(source_code)?;
    let res = analyze_file(ast);
    println!("{:?}", res);

    Ok(())
}
