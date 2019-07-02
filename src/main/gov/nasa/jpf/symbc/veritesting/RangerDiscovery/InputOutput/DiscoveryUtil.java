package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.Value;
import za.ac.sun.cs.green.expr.Operation;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.RNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.WRAPPERNODE;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config.folderName;
import static jkind.lustre.UnaryOp.NEGATIVE;
import static jkind.lustre.UnaryOp.NOT;

public class DiscoveryUtil {
    private static boolean firstTime = true;

    public static NamedType stringToLusterType(String typeName) {
        if (typeName.equals("int"))
            return NamedType.INT;
        else if (typeName.equals("float"))
            return NamedType.REAL;
        else if (typeName.equals("boolean"))
            return NamedType.BOOL;
        /*else if (typeName.equals("string"))
            return lusterStringType;*/
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static BinaryOp rangerBinaryOptoLusterOp(String s) {
        BinaryOp op;

        if (s.equals("!="))
            op = BinaryOp.fromString("<>");
        else if (s.equals("=="))
            op = BinaryOp.fromString("=");
        else if (s.equals("&&"))
            op = BinaryOp.fromString("and");
        else if (s.equals("||"))
            op = BinaryOp.fromString("or");
        else if (s.equals("%"))
            op = BinaryOp.fromString("mod");
        else
            op = BinaryOp.fromString(s);

        return op;
    }


    public static UnaryOp rangerUnaryyOptoLusterOp(String s) {
        UnaryOp op = null;

        if (s.equals("!"))
            op = UnaryOp.fromString("not");

        return op;
    }


    public static UnaryOp toLustreUnaryOp(Operation.Operator operator) {
        if (operator.toString().equals("-"))
            return NEGATIVE;
        else if (operator.toString().equals("!"))
            return NOT;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static BinaryOp toLustreBinaryOp(Operation.Operator operator) {
        if (operator == Operation.Operator.ADD)
            return BinaryOp.PLUS;
        else if (operator == Operation.Operator.SUB)
            return BinaryOp.MINUS;
        if (operator == Operation.Operator.MUL)
            return BinaryOp.MULTIPLY;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.DIVIDE;
        else if (operator == Operation.Operator.EQ)
            return BinaryOp.EQUAL;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.INT_DIVIDE;
        else if (operator == Operation.Operator.NE)
            return BinaryOp.NOTEQUAL;
        else if (operator == Operation.Operator.GT)
            return BinaryOp.GREATER;
        else if (operator == Operation.Operator.LT)
            return BinaryOp.LESS;
        else if (operator == Operation.Operator.GE)
            return BinaryOp.GREATEREQUAL;
        else if (operator == Operation.Operator.LE)
            return BinaryOp.LESSEQUAL;
        else if (operator == Operation.Operator.OR)
            return BinaryOp.OR;
        else if (operator == Operation.Operator.AND)
            return BinaryOp.AND;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static List<IdExpr> varDeclToIdExpr(List<VarDecl> varDeclList) {
        ArrayList<IdExpr> idExprList = new ArrayList<>();

        for (int i = 0; i < varDeclList.size(); i++) {
            idExprList.add(new IdExpr(varDeclList.get(i).id));
        }

        return idExprList;
    }

    public static IdExpr varDeclToIdExpr(VarDecl varDecl) {
        return new IdExpr(varDecl.id);
    }

    public static VarDecl IdExprToVarDecl(IdExpr idExpr, NamedType namedType) {
        return new VarDecl(idExpr.id, namedType);
    }


    public static boolean writeToFile(String fileName, String content) {
        fileName = folderName + "/" + fileName;
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName), "utf-8"))) {
            writer.write(content);
        } catch (FileNotFoundException e) {
            System.out.println("unable to write to file!");
            e.printStackTrace();
        } catch (IOException e) {
            System.out.println("unable to write to file!");
            e.printStackTrace();
        }
        return true;
    }


    public static Pair<VarDecl, Equation> replicateToOut(VarDecl varDecl, String stringName) {
        VarDecl newVarDecl = new VarDecl(stringName, varDecl.type);

        Equation eq = new Equation(varDeclToIdExpr(newVarDecl), varDeclToIdExpr(varDecl));

        return new Pair(newVarDecl, eq);
    }

    public static Node renameMainNode(String synthesis_spec, Node node) {
        return new Node(synthesis_spec, node.inputs, node.outputs, node.locals, node.equations, new ArrayList<>(), node.assertions, node.realizabilityInputs, node.contract, node.ivc);

    }


    public static Node findNode(List<Node> nodes, Node node) {
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(node.id))
                return nodes.get(i);
        }
        System.out.println("problem finding the node to repair!");
        return null;
    }


    public static void appendToFile(String fileName, String content) {
        boolean append;
        if (firstTime) {
            append = false;
            firstTime = false;
        } else append = true;

        try (FileWriter fw = new FileWriter(fileName, append);
             BufferedWriter bw = new BufferedWriter(fw);
             PrintWriter out = new PrintWriter(bw)) {
            out.println(content);
        } catch (IOException e) {
            System.out.println("Problem writing hole repairs to file! aborting!");
            assert false;
        }
    }

    public static Expr valueToExpr(Value value, Type type) {
        if (value instanceof BooleanValue)
            return new BoolExpr(((BooleanValue) value).value);
        else if (value instanceof IntegerValue)
            return new IntExpr(((IntegerValue) value).value);
        else if (value == null) {
            System.out.println("assuming default value");
            if (type == NamedType.BOOL)
                return new BoolExpr(false);
            else if (type == NamedType.INT)
                return new IntExpr(0);
            else {
                System.out.println("unsupported values type");
                assert false;
                return null;
            }
        } else {
            System.out.println("unsupported values type");
            assert false;
            return null;
        }
    }

    public static Ast getLastElementInMap(Map<Hole, List<Ast>> map, Object o) {
        List<Ast> value = map.get(o);
        if (value.size() != 0) // there has been a repair for the hole.
            return value.get(value.size() - 1);
        else
            return null;
    }

    /**
     * assigns initial value to a given equation.
     */
    public static Equation addInitToEq(Equation equation, Expr initialValue) {
        return new Equation(equation.lhs.get(0), new BinaryExpr(initialValue, BinaryOp.ARROW, equation.expr));
    }

    //tries to find the type of an expr inside a node.
    public static Type findExprType(Expr def, Node node) {
        if (def instanceof IntExpr)
            return NamedType.INT;
        else if (def instanceof BoolExpr)
            return NamedType.BOOL;
        else if (def instanceof IdExpr)
            return lookupExprType(def, node);
        else {
            System.out.println("unknown type for expr. Aborting!");
            assert false;
            return null;
        }
    }

    //looks up the type of a def by first looking into the inputs of the node then by checking the locals of the node.
    private static Type lookupExprType(Expr def, Node node) {
        VarDecl exprVarDecl = findInList(node.inputs, def);
        if (exprVarDecl == null) {
            exprVarDecl = findInList(node.locals, def);
            if (exprVarDecl == null) {
                System.out.println("unable to find the right type for expr. Aborting!");
                assert false;
            }
        }
        return exprVarDecl.type;
    }

    //takes an expr and tries to find its correponding type in the declartion list.
    private static VarDecl findInList(List<VarDecl> inputs, Expr def) {
        for (int i = 0; i < inputs.size() - 1; i++) {
            if (inputs.get(i).toString().equals(def.toString()))
                return inputs.get(i);
        }
        return null;
    }


}