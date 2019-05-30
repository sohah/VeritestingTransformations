package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.synthesis;

import jkind.lustre.Program;
import jkind.lustre.parsing.LustreParseUtil;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class SynthesisContract {

    public final Program holeProgram;

    public SynthesisContract(String fileName) throws IOException {
        holeProgram = ConstHoleVisitor.executeMain(LustreParseUtil.program(new String(Files.readAllBytes(Paths.get(fileName)
        ), "UTF-8")));
    }

    @Override
    public String toString(){
        return holeProgram.toString();
    }
}
