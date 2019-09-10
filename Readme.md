### Note:

This repo used to hold "JavaRanger", you can find it now [here](https://github.com/vaibhavbsharma/java-ranger). Going forward this repo contains the implementation of contract discovery described [here](https://github.com/sohah/ContractDiscovery). Sept. 10th 2019.

# JavaRanger for Symbolic PathFinder

JavaRanger collapses paths of regions of code that could be summarized statically. This allows for less path exploration by dynamic symbolic execution, thus allowing dynamic symbolic execution to be used over larger programs.

## JavaRanger Design:

This implementation of JavaRanger has a unique architecture and design, that is it has the following features:
1. Supproting an intermediate language: "RangerIR", which decompiles a CFG into an AST for later mainpulation by veritesting.
2. Allow different transformations over a veritesting region, which ensures transperency and enables reasoning about correctness and/or equivelance to the original program.
3. Enables high order regions, by de-referencing and inlining methods invocations.
4. Enables summarization of partial regions, allowing dynamic symbolic execution to only explore pieces of code that could not be statically summarized.
5. Supports SSA for fields that allows the summarization of nested fields. 


### JavaRanger Transformations

This JavaRanger project uses WALA as the static analysis engine to summarize regions of code. Summarization is done through different transformations applied on the initial Control Flow Graph, CFG, obtained by WALA. These transformations are:
1. CFG to AST Transformation: this is done by walking the CFG and creating a corresponding statement in RangerIR, at the end of this transformation a StaticRegion along with all its environment tables, input table, output table, var to slot table and variable type table.
2. Gamma Creation Transformation: this should be considered as a subtransformation of the previous tranformation where at the end of this transformation, phi instructions, are replaced by a Gamma instruction that captures the condition under which assignments of values are taken.
3. Substitution Transformation: in this transformation, constants and inputs are populated into the region, at the end of this transformation a DynamicRegion is generated that represents an instance 
4. Field Transformation: in this transformation, an SSA for fields is created to allow summarization of fields. At the end of this transformation, all "get" and "put" instructions should disappear leaving only field variables and assignment statements to them.
5. High Order Regions Transformation: in this transformation, method invocations are resolved and the intended method is inlined with the original region. At the end of this transformation, there should be no invoke instructions, instead, in their position, the method being invoked is inlined at that part.
6. SPFCases Transformations: This is two pass transformation, in the first pass, SPFCase statements are created for insturctions that are are hard to statically summaries and requires SPF exploration. In the second pass of this transformation SPFCases disappears only keeping a record of their predicates, leaving only instructions that could be statically summarized. At the end of this transformation, the Dynamic Region will be populated with the propriate SPFCase predicates, to account for all paths that requires SPF exploration, also all SPFCases statements are removed from the region statement.
7. Uniquness Transformation: in this transformation variable names are made unique to avoid conflicts that could result from hitting the same region again, i.e., inside a loop, but with different instantiated values.
8. Linearilization: in this transformation if-statements collapse by merging the statements of its "then" and the "else" sides. The idea being assignment of different variables are already reflected in the Gamma expressions and therefore if-statements are not longer needed.
9. To Green Expression Transformation: in this transformation, statements in the dynamic region are translated to Green expression and they should be ready to populate SPF accordingly.

This design that have the following benefits:
1. Ensures transperancy of different JavaRanger steps/transformations. 
2. Allows for checking invariants after each transformation.
3. Increases the oppurtunties over regions where JavaRanger could be applied.

### JavaRanger Documentation
For information about Java Documentation of the project please refer to https://sohah.github.io/VeritestingTransformations/. 
