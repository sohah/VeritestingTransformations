package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import jkind.lustre.NamedType;

import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.*;
import static gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract.lusterStringType;

public class DiscoveryUtil {
    public static NamedType stringToLusterType(String typeName){
        if(typeName.equals("int"))
            return lusterIntType;
        else if(typeName.equals("float"))
            return lusterFloatType;
        else if(typeName.equals("bool"))
            return lusterBoolType;
        else if(typeName.equals("string"))
            return lusterStringType;
        else{
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }
}
