package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import jkind.lustre.*;

import java.util.ArrayList;
import java.util.List;

public class HoleSpec {
    List<String> freeInput = new ArrayList<>();
    List<String> stateInput = new ArrayList<>();
    List<String> output = new ArrayList<>();
    List<String> holeInput = new ArrayList<>();

    public Node exposeNodeState(Node enclosedStateNode){

        String id = enclosedStateNode.id;
        List<VarDecl> inputs = enclosedStateNode.inputs;
        List<VarDecl> outputs = enclosedStateNode.outputs;
        List<VarDecl> locals = enclosedStateNode.locals;
        List<Equation> equations = enclosedStateNode.equations;
        List<String> properties = enclosedStateNode.properties;
        List<Expr> assertions = enclosedStateNode.assertions;
        List<String> ivc = enclosedStateNode.ivc;
        List<String> realizabilityInputs = enclosedStateNode.realizabilityInputs;
        Contract contract = enclosedStateNode.contract;

        inputs.addAll(locals);
        return new Node(id, inputs, outputs, null, equations, properties, assertions, realizabilityInputs, contract, ivc);

    }

}
