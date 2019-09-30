package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.UserLibrary.parsing;

import jkind.lustre.*;
import jkind.lustre.parsing.LustreBaseVisitor;
import jkind.lustre.parsing.LustreParseException;
import jkind.lustre.parsing.LustreParser.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;

import static java.util.stream.Collectors.toList;

public class LustreToAstVisitor extends LustreBaseVisitor<Object> {
	private String main;
	private Set<String> functionNames = new HashSet<>();

	public Program program(ProgramContext ctx) {
		List<TypeDef> types = types(ctx.typedef());
		List<Constant> constants = constants(ctx.constant());
		List<Function> functions = functions(ctx.function());
		List<Node> nodes = nodes(ctx.node());
		return new Program(loc(ctx), types, constants, functions, nodes, null, main);
	}

	private List<TypeDef> types(List<TypedefContext> ctxs) {
		List<TypeDef> types = new ArrayList<>();
		for (TypedefContext ctx : ctxs) {
			String id = ctx.ID().getText();
			Type type = topLevelType(id, ctx.topLevelType());
			types.add(new TypeDef(loc(ctx), id, type));
		}
		return types;
	}

	private List<Constant> constants(List<ConstantContext> ctxs) {
		List<Constant> constants = new ArrayList<>();
		for (ConstantContext ctx : ctxs) {
			String id = ctx.ID().getText();
			Type type = ctx.type() == null ? null : type(ctx.type());
			Expr expr = expr(ctx.expr());
			constants.add(new Constant(loc(ctx), id, type, expr));
		}
		return constants;
	}

	private List<Function> functions(List<FunctionContext> ctxs) {
		return ctxs.stream().map(this::function).collect(toList());
	}

	private List<Node> nodes(List<NodeContext> ctxs) {
		return ctxs.stream().map(this::node).collect(toList());
	}

	public Function function(FunctionContext ctx) {
		String id = eid(ctx.eID());
		List<VarDecl> inputs = varDecls(ctx.input);
		List<VarDecl> outputs = varDecls(ctx.output);
		functionNames.add(id);
		return new Function(loc(ctx), id, inputs, outputs);
	}

	public Node node(NodeContext ctx) {
		String id = ctx.ID().getText();
		List<VarDecl> inputs = varDecls(ctx.input);
		List<VarDecl> outputs = varDecls(ctx.output);
		List<VarDecl> locals = varDecls(ctx.local);
		List<Equation> equations = equations(ctx.equation());
		List<String> properties = properties(ctx.property());
		List<Expr> assertions = assertions(ctx.assertion());
		List<String> ivc = ivc(ctx.ivc());
		List<String> realizabilityInputs = realizabilityInputs(ctx.realizabilityInputs());
		Contract contract = null;
		if (!ctx.main().isEmpty()) {
			if (main == null) {
				main = id;
			} else {
				fatal(ctx.main(0), "node '" + main + "' already declared as --%MAIN");
			}
		}
		return new Node(loc(ctx), id, inputs, outputs, locals, equations, properties, assertions, realizabilityInputs,
				contract, ivc);
	}

	private List<VarDecl> varDecls(VarDeclListContext listCtx) {
		List<VarDecl> decls = new ArrayList<>();
		if (listCtx == null) {
			return decls;
		}

		for (VarDeclGroupContext groupCtx : listCtx.varDeclGroup()) {
			Type type = type(groupCtx.type());
			for (EIDContext id : groupCtx.eID()) {
				decls.add(new VarDecl(loc(id), eid(id), type));
			}
		}
		return decls;
	}

	private List<Equation> equations(List<EquationContext> ctxs) {
		List<Equation> equations = new ArrayList<>();
		for (EquationContext ctx : ctxs) {
			equations.add(equation(ctx));
		}
		return equations;
	}

	public Equation equation(EquationContext ctx) {
		List<IdExpr> lhs = lhs(ctx.lhs());
		Expr expr = expr(ctx.expr());
		return new Equation(loc(ctx), lhs, expr);
	}

	private List<IdExpr> lhs(LhsContext ctx) {
		List<IdExpr> lhs = new ArrayList<>();
		if (ctx != null) {
			for (EIDContext id : ctx.eID()) {
				lhs.add(new IdExpr(loc(id), eid(id)));
			}
		}
		return lhs;
	}

	private String eid(EIDContext id) {
		return (String) visit(id);
	}

	private List<String> properties(List<PropertyContext> ctxs) {
		List<String> props = new ArrayList<>();
		for (PropertyContext ctx : ctxs) {
			props.add(eid(ctx.eID()));
		}
		return props;
	}

	private List<Expr> assertions(List<AssertionContext> ctxs) {
		List<Expr> assertions = new ArrayList<>();
		for (AssertionContext ctx : ctxs) {
			assertions.add(expr(ctx.expr()));
		}
		return assertions;
	}

	private List<String> realizabilityInputs(List<RealizabilityInputsContext> ctxs) {
		if (ctxs.size() > 1) {
			fatal(ctxs.get(1), "at most one realizability statement allowed");
		}

		for (RealizabilityInputsContext ctx : ctxs) {
			List<String> ids = new ArrayList<>();
			for (TerminalNode ictx : ctx.ID()) {
				ids.add(ictx.getText());
			}
			return ids;
		}

		return null;
	}

	private List<String> ivc(List<IvcContext> ctxs) {
		if (ctxs.size() > 1) {
			fatal(ctxs.get(1), "at most one ivc statement allowed per node");
		}

		for (IvcContext ctx : ctxs) {
			List<String> ids = new ArrayList<>();
			for (EIDContext ictx : ctx.eID()) {
				ids.add(eid(ictx));
			}
			return ids;
		}

		return null;
	}

	private Type topLevelType(String id, TopLevelTypeContext ctx) {
		if (ctx instanceof PlainTypeContext) {
			PlainTypeContext pctx = (PlainTypeContext) ctx;
			return type(pctx.type());
		} else if (ctx instanceof RecordTypeContext) {
			RecordTypeContext rctx = (RecordTypeContext) ctx;
			Map<String, Type> fields = new HashMap<>();
			for (int i = 0; i < rctx.ID().size(); i++) {
				String field = rctx.ID(i).getText();
				if (fields.containsKey(field)) {
					fatal(ctx, "field declared multiple times: " + field);
				}
				fields.put(field, type(rctx.type(i)));
			}
			return new RecordType(loc(ctx), id, fields);
		} else if (ctx instanceof EnumTypeContext) {
			EnumTypeContext ectx = (EnumTypeContext) ctx;
			List<String> values = new ArrayList<>();
			for (TerminalNode node : ectx.ID()) {
				values.add(node.getText());
			}
			return new EnumType(loc(ctx), id, values);
		} else {
			throw new IllegalArgumentException(ctx.getClass().getSimpleName());
		}
	}

	private Type type(TypeContext ctx) {
		return (Type) ctx.accept(this);
	}

	@Override
	public Type visitIntType(IntTypeContext ctx) {
		return NamedType.INT;
	}

	@Override
	public Type visitSubrangeType(SubrangeTypeContext ctx) {
		BigInteger low = new BigInteger(ctx.bound(0).getText());
		BigInteger high = new BigInteger(ctx.bound(1).getText());
		return new SubrangeIntType(loc(ctx), low, high);
	}

	@Override
	public Type visitBoolType(BoolTypeContext ctx) {
		return NamedType.BOOL;
	}

	@Override
	public Type visitRealType(RealTypeContext ctx) {
		return NamedType.REAL;
	}

	@Override
	public Type visitArrayType(ArrayTypeContext ctx) {
		try {
			int index = Integer.parseInt(ctx.INT().getText());
			if (index == 0) {
				fatal(ctx, "array size must be non-zero");
			}
			return new ArrayType(loc(ctx), type(ctx.type()), index);
		} catch (NumberFormatException nfe) {
			fatal(ctx, "array size too large: " + ctx.INT().getText());
			return null;
		}
	}

	@Override
	public Type visitUserType(UserTypeContext ctx) {
		return new NamedType(loc(ctx), ctx.ID().getText());
	}

	public Expr expr(ExprContext ctx) {
		return (Expr) ctx.accept(this);
	}

	@Override
	public Expr visitIdExpr(IdExprContext ctx) {
		return new IdExpr(loc(ctx), ctx.ID().getText());
	}

	@Override
	public Expr visitIntExpr(IntExprContext ctx) {
		return new IntExpr(loc(ctx), new BigInteger(ctx.INT().getText()));
	}

	@Override
	public Expr visitRealExpr(RealExprContext ctx) {
		return new RealExpr(loc(ctx), new BigDecimal(ctx.REAL().getText()));
	}

	@Override
	public Expr visitBoolExpr(BoolExprContext ctx) {
		return new BoolExpr(loc(ctx), ctx.BOOL().getText().equals("true"));
	}

	@Override
	public Expr visitCastExpr(CastExprContext ctx) {
		return new CastExpr(loc(ctx), getCastType(ctx.op.getText()), expr(ctx.expr()));
	}

	private Type getCastType(String cast) {
		switch (cast) {
		case "real":
			return NamedType.REAL;
		case "floor":
			return NamedType.INT;
		default:
			throw new IllegalArgumentException("Unknown cast: " + cast);
		}
	}

	@Override
	public Expr visitCallExpr(CallExprContext ctx) {
		String name = eid(ctx.eID());
		List<Expr> args = new ArrayList<>();
		for (ExprContext arg : ctx.expr()) {
			args.add(expr(arg));
		}

		if (functionNames.contains(name)) {
			return new FunctionCallExpr(loc(ctx), name, args);
		} else {
			return new NodeCallExpr(loc(ctx), name, args);
		}
	}

	@Override
	public Expr visitCondactExpr(CondactExprContext ctx) {
		Expr clock = expr(ctx.expr(0));
		if (ctx.expr(1) instanceof CallExprContext) {
			CallExprContext callCtx = (CallExprContext) ctx.expr(1);
			Expr call = visitCallExpr(callCtx);
			if (call instanceof NodeCallExpr) {
				NodeCallExpr nodeCall = (NodeCallExpr) call;
				List<Expr> args = new ArrayList<>();
				for (int i = 2; i < ctx.expr().size(); i++) {
					args.add(expr(ctx.expr(i)));
				}
				return new CondactExpr(loc(ctx), clock, nodeCall, args);
			}
		}

		fatal(ctx, "second argument to condact must be a node call");
		return null;
	}

	@Override
	public Expr visitRecordAccessExpr(RecordAccessExprContext ctx) {
		return new RecordAccessExpr(loc(ctx), expr(ctx.expr()), ctx.ID().getText());
	}

	@Override
	public Expr visitRecordUpdateExpr(RecordUpdateExprContext ctx) {
		return new RecordUpdateExpr(loc(ctx), expr(ctx.expr(0)), ctx.ID().getText(), expr(ctx.expr(1)));
	}

	@Override
	public Expr visitArrayAccessExpr(ArrayAccessExprContext ctx) {
		return new ArrayAccessExpr(loc(ctx), expr(ctx.expr(0)), expr(ctx.expr(1)));
	}

	@Override
	public Expr visitArrayUpdateExpr(ArrayUpdateExprContext ctx) {
		return new ArrayUpdateExpr(loc(ctx), expr(ctx.expr(0)), expr(ctx.expr(1)), expr(ctx.expr(2)));
	}

	@Override
	public Expr visitPreExpr(PreExprContext ctx) {
		return new UnaryExpr(loc(ctx), UnaryOp.PRE, expr(ctx.expr()));
	}

	@Override
	public Expr visitNotExpr(NotExprContext ctx) {
		return new UnaryExpr(loc(ctx), UnaryOp.NOT, expr(ctx.expr()));
	}

	@Override
	public Expr visitNegateExpr(NegateExprContext ctx) {
		return new UnaryExpr(loc(ctx), UnaryOp.NEGATIVE, expr(ctx.expr()));
	}

	@Override
	public Expr visitBinaryExpr(BinaryExprContext ctx) {
		String op = ctx.op.getText();
		Expr left = expr(ctx.expr(0));
		Expr right = expr(ctx.expr(1));
		return new BinaryExpr(loc(ctx), left, BinaryOp.fromString(op), right);
	}

	@Override
	public Expr visitIfThenElseExpr(IfThenElseExprContext ctx) {
		return new IfThenElseExpr(loc(ctx), expr(ctx.expr(0)), expr(ctx.expr(1)), expr(ctx.expr(2)));
	}

	@Override
	public Expr visitRecordExpr(RecordExprContext ctx) {
		Map<String, Expr> fields = new HashMap<>();
		for (int i = 0; i < ctx.expr().size(); i++) {
			String field = ctx.ID(i + 1).getText();
			if (fields.containsKey(field)) {
				fatal(ctx, "field assigned multiple times: " + field);
			}
			fields.put(field, expr(ctx.expr(i)));
		}
		return new RecordExpr(loc(ctx), ctx.ID(0).getText(), fields);
	}

	@Override
	public Expr visitArrayExpr(ArrayExprContext ctx) {
		List<Expr> elements = new ArrayList<>();
		for (int i = 0; i < ctx.expr().size(); i++) {
			elements.add(expr(ctx.expr(i)));
		}
		return new ArrayExpr(loc(ctx), elements);
	}

	@Override
	public Expr visitTupleExpr(TupleExprContext ctx) {
		// Treat singleton tuples as simply parentheses. This increases parsing
		// performance by not having to decide between parenExpr and tupleExpr.
		if (ctx.expr().size() == 1) {
			return expr(ctx.expr(0));
		}

		List<Expr> elements = new ArrayList<>();
		for (int i = 0; i < ctx.expr().size(); i++) {
			elements.add(expr(ctx.expr(i)));
		}
		return new TupleExpr(loc(ctx), elements);
	}

	@Override
	public String visitBaseEID(BaseEIDContext ctx) {
		return ctx.ID().getText();
	}

	@Override
	public String visitArrayEID(ArrayEIDContext ctx) {
		return visit(ctx.eID()) + "[" + ctx.INT().getText() + "]";
	}

	@Override
	public String visitRecordEID(RecordEIDContext ctx) {
		return visit(ctx.eID()) + "." + ctx.ID().getText();
	}

	protected Location loc(ParserRuleContext ctx) {
		Token token = ctx.getStart();
		if (ctx instanceof BinaryExprContext) {
			BinaryExprContext binExpr = (BinaryExprContext) ctx;
			token = binExpr.op;
		}
		return new Location(token.getLine(), token.getCharPositionInLine());
	}

	private void fatal(ParserRuleContext ctx, String text) {
		throw new LustreParseException(loc(ctx), text);
	}
}
