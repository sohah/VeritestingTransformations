package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Util;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Config;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Queries.ARepair.synthesis.Hole;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import jkind.api.JKindApi;
import jkind.api.results.JKindResult;
import jkind.lustre.*;
import jkind.lustre.values.BooleanValue;
import jkind.lustre.values.IntegerValue;
import jkind.lustre.values.Value;
import org.eclipse.core.runtime.NullProgressMonitor;
import za.ac.sun.cs.green.expr.Operation;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

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
        else if (s.equals("/")) //supporting only integer division.
            op = BinaryOp.fromString("div");
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


    public static boolean writeToFile(String fileName, String content, boolean minimal) {
        String directory;

        if (minimal)
            directory = folderName + "output/" + Config.currFaultySpec + "/minimal/";

        else
            directory = folderName + "output/" + Config.currFaultySpec + "/";


        fileName = directory + fileName;

        try {

            if (!Files.exists(Paths.get(directory)))
                Files.createDirectories(Paths.get(directory));

            Writer writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fileName), "utf-8"));
            writer.write(content);
            writer.close();
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

    public static Node renameNode(String synthesis_spec, Node node) {
        return new Node(synthesis_spec, node.inputs, node.outputs, node.locals, node.equations, new ArrayList<>(), node.assertions, node.realizabilityInputs, node.contract, node.ivc);

    }

    public static Node addProperty(String property, Node node) {
        List<String> newProperties = new ArrayList<>();
        newProperties.add(property);
        return new Node(node.id, node.inputs, node.outputs, node.locals, node.equations, newProperties, node.assertions, node.realizabilityInputs, node.contract, node.ivc);

    }

    public static Program addNode(Program pgm, Node newNode) {
        List<Node> newNodes = new ArrayList(pgm.nodes);
        newNodes.add(newNode);
        return new Program(pgm.location, pgm.types, pgm.constants, pgm.functions, newNodes, pgm.repairNodes, pgm.main);
    }

    public static List<Node> removeNode(Program pgm, Node node) {
        List<Node> newNodes = new ArrayList<>();
        List<Node> oldNodes = pgm.nodes;
        for (int i = 0; i < oldNodes.size(); i++) { //filtering away unwanted nodes.
            if (!oldNodes.get(i).id.equals(node.id))
                newNodes.add(oldNodes.get(i));
        }
        return newNodes;
    }


    public static List<Node> removeNodeStr(List<Node> oldNodes, String nodeName) {
        List<Node> newNodes = new ArrayList<>();
        for (int i = 0; i < oldNodes.size(); i++) { //filtering away unwanted nodes.
            if (!oldNodes.get(i).id.equals(nodeName))
                newNodes.add(oldNodes.get(i));
        }
        return newNodes;
    }

    public static Node findNodeStr(List<Node> nodes, String nodeName) {
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(nodeName))
                return nodes.get(i);
        }
        return null;
    }


    public static Node findNode(List<Node> nodes, Node node) {
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(node.id))
                return nodes.get(i);
        }
        System.out.println("problem finding the node to repair!");
        return null;
    }


    public static RepairNode findRepairNodeDef(List<RepairNode> nodes, String node) {
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(node))
                return nodes.get(i);
        }
        System.out.println("problem finding the node to repair!");
        return null;
    }


    public static Equation findEqWithLhs(List<Equation> equations, String lhs) {
        for (int i = 0; i < equations.size(); i++) {
            if (equations.get(i).lhs.get(0).toString().equals(lhs))
                return equations.get(i);
        }
        return null;
    }


    public static List<Equation> removeEqWithLhs(List<Equation> equations, String lhs) {
        List<Equation> newEquation = new ArrayList<>();

        for (int i = 0; i < equations.size(); i++) {
            if (!equations.get(i).lhs.get(0).toString().equals(lhs))
                newEquation.add(equations.get(i));
        }
        return newEquation;
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
    public static Type findExprType(Expr def, Node node, Program pgm) {
        if (def instanceof IntExpr)
            return NamedType.INT;
        else if (def instanceof BoolExpr)
            return NamedType.BOOL;
        else if (def instanceof IdExpr)
            return lookupExprType(def, node, pgm);
        else {
            System.out.println("unknown type for expr. Aborting!");
            assert false;
            return null;
        }
    }

    //looks up the type of a def by first looking into the inputs of the node then by checking the locals of the node.
    public static Type lookupExprType(Expr def, Node node, Program pgm) {
        VarDecl exprVarDecl = findInList(node.inputs, def);
        if (exprVarDecl == null) {
            exprVarDecl = findInList(node.locals, def);
            if (exprVarDecl == null)
                exprVarDecl = findConstInList(pgm.constants, def);
            if (exprVarDecl == null)
                exprVarDecl = findInList(node.outputs, def);
            if (exprVarDecl == null) {
                System.out.println("unable to find the right type for expr. Aborting!");
                assert false;
            }
        }
        return exprVarDecl.type;
    }

    //takes an expr and tries to find its correponding type in the declartion list.

    private static VarDecl findInList(List<VarDecl> inputs, Expr def) {
        for (int i = 0; i < inputs.size(); i++) {
            if (inputs.get(i).id.equals(def.toString()))
                return inputs.get(i);
        }
        return null;
    }


    public static Equation findEqInList(List<Equation> eqs, String lhs) {
        for (int i = 0; i < eqs.size(); i++) {
            if (eqs.get(i).lhs.get(0).toString().equals(lhs))
                return eqs.get(i);
        }
        return null;
    }

    //takes an expr and tries to find its correponding type in the declartion list.
    private static VarDecl findConstInList(List<Constant> inputs, Expr def) {
        for (int i = 0; i < inputs.size(); i++) {
            if (inputs.get(i).id.equals(def.toString())) {
                if (inputs.get(i).type != null)
                    return new VarDecl(inputs.get(i).id, inputs.get(i).type);
                else if (inputs.get(i).expr instanceof IntExpr)
                    return new VarDecl(inputs.get(i).id, NamedType.INT);
                else if (inputs.get(i).expr instanceof BoolExpr)
                    return new VarDecl(inputs.get(i).id, NamedType.BOOL);
            }
        }
        return null;
    }

    /**
     * computes the permutation of a specific size, where each entry has a corresponding value of 1 or zero.
     * all possible permutations are added to the permutation list.
     *
     * @param size
     * @return
     */
    public static List<List<Character>> computePermutation(int size) {
        if (size < 1) {
            System.out.println("cannot compute permutation over an empty list");
            assert false;
        }

        List<List<Character>> permutationList = new ArrayList<>();
        for (int i = 0; i < Math.pow(2, size); i++) {
            String permutation = String.format("%" + size + "s", Integer.toBinaryString(i)).replace(' ', '0');
            permutationList.add(permutation.chars().mapToObj(e -> (char) e).collect(Collectors.toList()));
        }

        return permutationList;
    }

    public static JKindResult callJkind(String fileName, boolean kInductionOn, int maxK, boolean minimal, boolean existsQuery) {
        File file1;

        if (!minimal)
            file1 = new File(folderName + "/output/" + Config.currFaultySpec + "/" + fileName);
        else
            file1 = new File(folderName + "/output/" + Config.currFaultySpec + "/minimal/" + fileName);

        if (minimal)
            return runJKind(file1, kInductionOn, maxK, existsQuery);
        else // ensuring that you can't have a exists query true, without having a minimal query
            return runJKind(file1, kInductionOn, maxK, false);
    }

    //exists query is used only when it is a minimal query and its job is to turn off the pdr.
    private static JKindResult runJKind(File file, boolean kInductionOn, int maxK, boolean existsQuery) {

/*
        String[] jkindArgs = new String[5];

        jkindArgs[0] = "-jkind";
        jkindArgs[1] = folderName + contractMethodName + ".lus";
        jkindArgs[2] = "-solver";
        jkindArgs[3] = "z3";
        jkindArgs[4] = "-scratch";
        Main.main(jkindArgs);
*/

        JKindApi api = new JKindApi();
        JKindResult result = new JKindResult("");
        if (!kInductionOn) { // I have not yet noticed considerable benefit from stopping kInduction on the there
            // exists query. I'm turning it off for now.
         //   api.disableKInduction();
        }


        api.setJKindJar("../../../jkind/jkind.jar");

        api.disableSlicing();

        // useful in minimization query where we want to not halt in the last query, for that we need to stop
        // generation of pdr while checking the needed steps in BMC.

        if(existsQuery){
            maxK = maxK==0 ? 5 : maxK*3;
            api.setPdrMax(0);
        }


        if (maxK != -1) //if not set
            api.setN(maxK);

        //api.setSolver(SolverOption.Z3);

        //api.setTimeout(300);
        // The monitor is only currently used to detect cancellation NullProgressMonitor

        api.execute(file, result, new NullProgressMonitor());

        return result;
    }


}