<?xml version="1.0" encoding="UTF-8"?>
<PlexilPlan xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
            xmlns:tr="extended-plexil-translator">
   <GlobalDeclarations LineNo="3" ColNo="0">
      <CommandDeclaration LineNo="3" ColNo="0">
         <Name>rover_drive</Name>
         <Parameter>
            <Type>Integer</Type>
         </Parameter>
      </CommandDeclaration>
      <CommandDeclaration LineNo="4" ColNo="0">
         <Name>rover_stop</Name>
      </CommandDeclaration>
      <CommandDeclaration LineNo="5" ColNo="0">
         <Name>take_navcam</Name>
      </CommandDeclaration>
      <CommandDeclaration LineNo="6" ColNo="0">
         <Name>take_pancam</Name>
      </CommandDeclaration>
      <StateDeclaration LineNo="8" ColNo="5">
         <Name>time</Name>
         <Return>
            <Name>_return_0</Name>
            <Type>Real</Type>
         </Return>
      </StateDeclaration>
      <StateDeclaration LineNo="9" ColNo="5">
         <Name>temperature</Name>
         <Return>
            <Name>_return_0</Name>
            <Type>Real</Type>
         </Return>
      </StateDeclaration>
      <StateDeclaration LineNo="10" ColNo="8">
         <Name>target_in_view</Name>
         <Return>
            <Name>_return_0</Name>
            <Type>Boolean</Type>
         </Return>
      </StateDeclaration>
   </GlobalDeclarations>
   <Node NodeType="NodeList" epx="Concurrence" LineNo="14" ColNo="0">
      <NodeId>DriveToTarget</NodeId>
      <VariableDeclarations>
         <DeclareVariable LineNo="15" ColNo="2">
            <Name>drive_done</Name>
            <Type>Boolean</Type>
            <InitialValue>
               <BooleanValue>false</BooleanValue>
            </InitialValue>
         </DeclareVariable>
         <DeclareVariable LineNo="15" ColNo="2">
            <Name>timeout</Name>
            <Type>Boolean</Type>
            <InitialValue>
               <BooleanValue>false</BooleanValue>
            </InitialValue>
         </DeclareVariable>
      </VariableDeclarations>
      <NodeBody>
         <NodeList>
            <Node NodeType="Command" LineNo="17" ColNo="9">
               <NodeId>Drive</NodeId>
               <NodeBody>
                  <Command>
                     <Name>
                        <StringValue>rover_drive</StringValue>
                     </Name>
                     <Arguments LineNo="17" ColNo="21">
                        <IntegerValue>10</IntegerValue>
                     </Arguments>
                  </Command>
               </NodeBody>
            </Node>
            <Node NodeType="NodeList" epx="Concurrence" LineNo="20" ColNo="2">
               <NodeId>StopForTimeout</NodeId>
               <StartCondition>
                  <GE>
                     <LookupOnChange>
                        <Name>
                           <StringValue>time</StringValue>
                        </Name>
                        <Tolerance>
                           <RealValue>0.1</RealValue>
                        </Tolerance>
                     </LookupOnChange>
                     <IntegerValue>10</IntegerValue>
                  </GE>
               </StartCondition>
               <NodeBody>
                  <NodeList>
                     <Node NodeType="Command" LineNo="22" ColNo="10">
                        <NodeId>Stop</NodeId>
                        <NodeBody>
                           <Command>
                              <Name>
                                 <StringValue>rover_stop</StringValue>
                              </Name>
                           </Command>
                        </NodeBody>
                     </Node>
                     <Node NodeType="Assignment" LineNo="24" ColNo="20">
                        <NodeId>SetTimeoutFlag</NodeId>
                        <NodeBody>
                           <Assignment>
                              <BooleanVariable>timeout</BooleanVariable>
                              <BooleanRHS>
                                 <BooleanValue>true</BooleanValue>
                              </BooleanRHS>
                           </Assignment>
                        </NodeBody>
                     </Node>
                  </NodeList>
               </NodeBody>
            </Node>
            <Node NodeType="NodeList" epx="Concurrence" LineNo="28" ColNo="2">
               <NodeId>StopForTarget</NodeId>
               <StartCondition>
                  <LookupOnChange>
                     <Name>
                        <StringValue>target_in_view</StringValue>
                     </Name>
                  </LookupOnChange>
               </StartCondition>
               <SkipCondition>
                  <BooleanVariable>timeout</BooleanVariable>
               </SkipCondition>
               <NodeBody>
                  <NodeList>
                     <Node NodeType="Command" LineNo="32" ColNo="10">
                        <NodeId>Stop</NodeId>
                        <NodeBody>
                           <Command>
                              <Name>
                                 <StringValue>rover_stop</StringValue>
                              </Name>
                           </Command>
                        </NodeBody>
                     </Node>
                     <Node NodeType="Assignment" LineNo="33" ColNo="18">
                        <NodeId>SetDriveFlag</NodeId>
                        <NodeBody>
                           <Assignment>
                              <BooleanVariable>drive_done</BooleanVariable>
                              <BooleanRHS>
                                 <BooleanValue>true</BooleanValue>
                              </BooleanRHS>
                           </Assignment>
                        </NodeBody>
                     </Node>
                  </NodeList>
               </NodeBody>
            </Node>
            <Node NodeType="Command" LineNo="40" ColNo="4">
               <NodeId>TakeNavcam</NodeId>
               <StartCondition>
                  <BooleanVariable>timeout</BooleanVariable>
               </StartCondition>
               <NodeBody>
                  <Command>
                     <Name>
                        <StringValue>take_navcam</StringValue>
                     </Name>
                  </Command>
               </NodeBody>
               <SkipCondition>
                  <BooleanVariable>drive_done</BooleanVariable>
               </SkipCondition>
            </Node>
            <Node NodeType="Command" LineNo="47" ColNo="4">
               <NodeId>TakePancam</NodeId>
               <StartCondition>
                  <BooleanVariable>drive_done</BooleanVariable>
               </StartCondition>
               <NodeBody>
                  <Command>
                     <Name>
                        <StringValue>take_pancam</StringValue>
                     </Name>
                  </Command>
               </NodeBody>
               <SkipCondition>
                  <BooleanVariable>timeout</BooleanVariable>
               </SkipCondition>
            </Node>
         </NodeList>
      </NodeBody>
   </Node>
</PlexilPlan>