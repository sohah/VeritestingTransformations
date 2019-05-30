package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract;
import jkind.lustre.Program;
import jkind.lustre.parsing.LustreParseUtil;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class SynthesisContract {

    public final Program holeProgram;
    public final Contract contract;

    public SynthesisContract(gov.nasa.jpf.symbc.veritesting.RangerDiscovery.Contract contract, String fileName) throws IOException {
        holeProgram = ConstHoleVisitor.executeMain(LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(fileName)
        ), "UTF-8")));
       this.contract = contract;
    }

    @Override
    public String toString(){
        return holeProgram.toString();
    }
}
