/*
 * Copyright 2018 The Closure Compiler Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.google.javascript.jscomp;

//import com.google.common.base.Preconditions;
import com.google.javascript.rhino.Token;
import com.google.javascript.rhino.Node;
import com.google.javascript.jscomp.NodeTraversal.ScopedCallback;
import com.google.javascript.jscomp.ControlFlowGraph.AbstractCfgNodeTraversalCallback;
import com.google.javascript.jscomp.ControlFlowGraph.Branch;
import com.google.javascript.jscomp.NodeTraversal.AbstractShallowCallback;
import com.google.javascript.jscomp.NodeTraversal.AbstractPostOrderCallback;
//import java.util.MultiMap;
import java.io.BufferedWriter;
import java.util.HashMap;
import java.util.Vector;
import java.util.*;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import com.google.gson.Gson;
import java.lang.Integer;
//import org.json.simple.JSONObject;

/** Removes the contets of weak source files. */
class TaintAnalysisPass implements CompilerPass , ScopedCallback {
    private static final String sourceFunction= "retSource";
    private static final String sinkFunction= "sink";
    private static final String sourceThatMust= "sources_that_must_reach_sinks";
    private static final String sourceThatMay= "sources_that_may_reach_sinks";

    private TaintAnalysis reachingDef;
  private final AbstractCompiler compiler;
  private ControlFlowGraph<Node> cfg;
  public int x ;
    public final String blankOrNewLine = "\n";
    public String singleIndent = "    ";
    private String currentIndent = " ";
  public int isMayReach  = 0;
  public  String strName = "";
   public String retInput= "";
    public String nextInput = "";
    public int firsttime = 0;
    List<String> SourceVaraible = new ArrayList<String>();
    List<String> MustAliasSourceVaraible = new ArrayList<String>();
    public List<String> taintedVariable  = new ArrayList<String>();
    private final Map<String, Integer> MapOfTaintedVaraible = new HashMap<String, Integer>();

    private final Map<String, List<String>> MapOfVaraible = new HashMap<String, List<String>>();
    private final Map<String, Integer> MapVaraibleLineNumber = new HashMap<String, Integer>();
    private final Map<String, Integer> MapAliasVaraibleBlockNumber = new HashMap<String, Integer>();
    private final Map<String, Integer> MapVaraibleLineNumberBlock = new HashMap<String, Integer>();
    private final Map<String, Integer> MapOfAliasNodeIf = new HashMap<String, Integer>();
   // private final Map<String, Integer> MapOfAliasNodeREachableOrNot = new HashMap<String, Integer>();

    // Map<String, List<String>> m = new HashMap<String, List<String>>();
//  public  MultiMap multiMap = new MultiValueMap();
  public TaintAnalysisPass(AbstractCompiler compiler) {
    this.compiler = compiler;
  }
  @Override
  public void exitScope(NodeTraversal t) {}
  @Override
  public void enterScope(NodeTraversal t) {}
  @Override
  public final boolean shouldTraverse(NodeTraversal t, Node n, Node parent) {
    return !n.isScript() || !t.getInput().isExtern();
  }


  @Override
  public void visit(NodeTraversal t, Node n, Node parent) {
    // TODO(user): While the helpers do a subtree traversal on the AST, the
    // compiler pass itself only traverse the AST to look for function
    // declarations to perform dataflow analysis on. We could combine
    // the traversal in DataFlowAnalysis's computeEscaped later to save some
    // time.

  }
  @Override
  public void process(Node externs, Node root) {
      NodeTraversal.traverse(compiler, root, new Traversal());
  }



  private class Traversal extends AbstractPostOrderCallback {

      public String getOutputFileName(NodeTraversal traversal) {
          String orgFileName = traversal.getSourceName();
          String outputFileName = orgFileName.substring(0, orgFileName.lastIndexOf("/") + 1) + "Output.json";
          return outputFileName;
      }


      public void printAsJson(String functionName, NodeTraversal t) {
//TO print the output to file.
          try {

              File f1 = new File(getOutputFileName(t));
              //To create new file on each run
                    if(firsttime == 0)
                    {
                        if (f1.exists()) {
                            f1.delete();
                        }
                        if (!f1.exists()) {
                            f1.createNewFile();
                        }
                        FileWriter fileWritter = new FileWriter(getOutputFileName(t), true);
                        fileWritter.write("{" + blankOrNewLine);
                        fileWritter.close();

                    }
                    FileWriter fileWritter = new FileWriter(getOutputFileName(t), true);
                    if(firsttime > 0) {
                        fileWritter.write(","+blankOrNewLine);
                }
           //   fileWritter.write("{" + blankOrNewLine);
              fileWritter.write(currentIndent);
              fileWritter.write("\"" + functionName + "\": {" + blankOrNewLine);
              fileWritter.write(singleIndent);
              fileWritter.write("\"" + sourceThatMust + "\": [");
              Iterator mIterator = MapOfTaintedVaraible.entrySet().iterator();
              int firstVar = 0;
              while (mIterator.hasNext()) {
                  Map.Entry mapElement = (Map.Entry) mIterator.next();
                  //If the value is one then it is must reach
                  if((Integer)(mapElement.getValue()) == 1 /*|| isMayReach !=1*/ )
                  {
                      if(firstVar > 0)
                          fileWritter.write(",");

                      fileWritter.write("\"" + mapElement.getKey() + "\"");
                      firstVar = firstVar +1;
                  }
              }



              fileWritter.write("],");
              fileWritter.write(blankOrNewLine);
              fileWritter.write(singleIndent);
              fileWritter.write("\"" + sourceThatMay + "\": [");
              mIterator = MapOfTaintedVaraible.entrySet().iterator();
              firstVar = 0;
              while (mIterator.hasNext()) {
                  Map.Entry mapElement = (Map.Entry) mIterator.next();
                  ///  int Checkmaymust =  mapElement.getValue();
                  if (/*isMayReach == 1 */(Integer)(mapElement.getValue()) == 0 || (Integer)(mapElement.getValue()) == 1 )
                  {
                      if(firstVar > 0)
                          fileWritter.write(",");
                      fileWritter.write("\"" + mapElement.getKey() + "\"");
                      firstVar = firstVar + 1;
                  }

              }
              fileWritter.write("]");
              fileWritter.write(blankOrNewLine);
              fileWritter.write(currentIndent);
              fileWritter.write("}");
              fileWritter.close();
          } catch (IOException e) {
              e.printStackTrace();
          }
          firsttime  = firsttime + 1;
      }
      public int checkMayReach(Node n) {
          //Check if there is any condtion in calling of sink function
          for (Node c = n.getParent(); c != null; c = c.getParent()) {
              if (c.getToken() == Token.BLOCK && c.getParent() != null && ((c.getParent()).getToken() == Token.IF || (c.getParent()).getToken() == Token.CASE || (c.getParent()).getToken() == Token.FOR)) {
                  return 1;
                 // break;
              }
          }
          return 0;
      }

      public void addVaraibleToMap(String MainName, String OtherName) {
          List<String> l = MapOfVaraible.get(MainName);
          if (l == null)
              MapOfVaraible.put(MainName, l = new ArrayList<String>());
          else {
              if(!l.contains(OtherName))
              l.add(OtherName);
          }
      }
      public void storeBlockNumber(Node n)
      {
          int blockNumer;
          for (Node p = n.getParent(); p != null; p = p.getParent()) {
              if(p.getToken() == Token.BLOCK)
              {
                  blockNumer    = p.getLineno();
                  MapAliasVaraibleBlockNumber.put(n.getString(), blockNumer );
                  break;
              }
          }
      }
      public void checkTaintedVaraibles(String varName, int sinkFunctionBlockNumber,int sinkFunctionCondition) {
          boolean isKeyPresent = MapOfVaraible.containsKey(varName);
          //if variable is directly present i.e x = retsource() sink(x)
          if (isKeyPresent) {
              int p = 1;
              int i = MapVaraibleLineNumber.get(varName);
              String finalName =varName + "@" + i;
              if(!MapOfTaintedVaraible.containsKey(finalName)) {
                  if(sinkFunctionBlockNumber  == MapVaraibleLineNumberBlock.get(varName) /*&& sinkFunctionCondition == 0*/)
                  MapOfTaintedVaraible.put(finalName,1);
                  else MapOfTaintedVaraible.put(finalName,0);
              }
          } else {
    //if variable is not directly the varaible that stores the retSourece() but another varaible that uses this varaible
    //eg  x = retsource() ; y = x+1 ; sink(y);
              Iterator mIterator = MapOfVaraible.entrySet().iterator();
              while (mIterator.hasNext()) {
                  Map.Entry mapElement = (Map.Entry) mIterator.next();
                  List<String> l = ((List<String>) mapElement.getValue());
                  boolean ifPresentWithOtherName = l.contains(varName);
                  if (ifPresentWithOtherName) {
                      String varNameOrg = (String) mapElement.getKey();
                      int i = MapVaraibleLineNumber.get(varNameOrg);
                      String finalName =varNameOrg + "@" + i;
                      if(!MapOfTaintedVaraible.containsKey(finalName)) {
                       //   if(sinkFunctionBlockNumber  == MapVaraibleLineNumberBlock.get(varNameOrg) && sinkFunctionCondition == 0)
                          if(MustAliasSourceVaraible.contains(varName)) //checks if variable is present in both if and else to identify must and may reach
                          {
                              MapOfTaintedVaraible.put(finalName, 1);
                          }
                          else {
                              if (sinkFunctionBlockNumber == MapAliasVaraibleBlockNumber.get(varName) ) //checks if the variable and sink function both are in same block to identify must and may reach
                                  MapOfTaintedVaraible.put(finalName, 1);
                              else MapOfTaintedVaraible.put(finalName, 0);
                          }
                      }
                  }
              }
          }
      }

      //To check if variable is present in both if and else blocks
      public void checkAliasForIfElse(Node n) {
String nameOfVaraible = n.getString();
          for (Node c = n.getParent(); c != null; c = c.getParent()) {

              if (c.getToken() == Token.IF) {
                  int blockNumer = c.getLineno();
                  if (!MapOfAliasNodeIf.containsKey(nameOfVaraible)) {
                      MapOfAliasNodeIf.put(nameOfVaraible,blockNumer);
                  }
                  else
                  {
                      int i = MapOfAliasNodeIf.get(nameOfVaraible);
                      if(blockNumer == i)
                      {
                          if(!MustAliasSourceVaraible.contains(nameOfVaraible)) {
                              MustAliasSourceVaraible.add(nameOfVaraible);
                          }
                      }
                  }
              }
          }
      }

 //checks if the retsource() result variable is used by another variable, stores block number of that vraible in map
//checks checkAliasForIfElse that is whether variable is used in both if or else for identifying may and must
      public void checkWhichStructVarContainThisVar(Node n) {
          String orgName = n.getString();

          for(Node c = n.getParent(); c !=null;c =c.getParent())
      {
          if(c.getToken() == Token.ASSIGN && c.getFirstChild() != null)
          {
              if(c.getFirstChild().getToken() == Token.NAME )
                  storeBlockNumber(c.getFirstChild());
                  addVaraibleToMap(orgName, c.getFirstChild().getString());
                  checkAliasForIfElse(c.getFirstChild());
              break;
          }
          if (c.getToken() == Token.NAME && c.getParent() != null && (c.getParent()).getToken() == Token.VAR) {
              storeBlockNumber(c);
              addVaraibleToMap(orgName, c.getString());
              checkAliasForIfElse(c);
              break;
          }

      }
  }
      //checks if the retsource() result variable is used by another variable, stores block number of that vraible in map
//checks checkAliasForIfElse that is whether variable is used in both if or else for identifying may and must
      public void checkWhichStructVarContainOtherVar(Node n,String orgName) {
          //String orgName = n.getString();

          for(Node c = n.getParent(); c !=null;c =c.getParent())
          { if(c.getToken() == Token.ASSIGN && c.getFirstChild() != null)
            {
              if(c.getFirstChild().getToken() == Token.NAME )
                  storeBlockNumber(c.getFirstChild());
                  addVaraibleToMap(orgName, c.getFirstChild().getString());
                checkAliasForIfElse(c.getFirstChild());
                    break;
            }

              else if (c.getToken() == Token.NAME && c.getParent() != null && (c.getParent()).getToken() == Token.VAR) {
              storeBlockNumber(c);
                  addVaraibleToMap(orgName, c.getString());
              checkAliasForIfElse(c);
                  break;
              }

          }
      }

      //find variable that is storing retsource result
//Puts into the map
      public void findRetSourceVaraible(Node n) {
    for (Node c = n.getParent(); c != null; c = c.getParent()) {
        if (c.getToken() == Token.NAME && c.getParent() != null && (c.getParent()).getToken() == Token.VAR) {
            String varName = c.getString();
            SourceVaraible.add(varName);
            if(!MapOfVaraible.containsKey(varName))
            MapOfVaraible.put(varName,new ArrayList<String>()); //for storing the other variable that uses this retSource varaible
            int linenumber = n.getLineno();
            if(!MapVaraibleLineNumber.containsKey(varName))
            MapVaraibleLineNumber.put(varName,linenumber); //Stores the line number of varaible in another map
            for (Node p = c.getParent(); p != null; p = p.getParent()) {
                //Identifies in which block the varaible is present and puts into the map of line number block( used for identify may and must)
                if(p.getToken() == Token.BLOCK)
                {
                    int linenumberP = p.getLineno();
                    MapVaraibleLineNumberBlock.put(varName,linenumberP);
                    break;
                }
            }
            break;
        }

    }

}
@Override
    public void visit(NodeTraversal t, Node n, Node parent) {
          if(n.getToken() == Token.ROOT) //end the output file
          {
              try{
              FileWriter fileWritter = new FileWriter(getOutputFileName(t), true);
              fileWritter.write(blankOrNewLine + "}");
              fileWritter.close();
              }
              catch (IOException e) {
                  e.printStackTrace();
              }
          }
       //end of a function enter the function details to the file ,  clear all the previous stored data and
    if(n.getToken() == Token.BLOCK && (n.getParent()).getToken() == Token.FUNCTION
            && ((n.getParent()).getFirstChild()).getString() != sourceFunction && ((n.getParent()).getFirstChild()).getString() != sinkFunction )
    {
        int linenumber = n.getLineno();
        String functionName = ((n.getParent()).getFirstChild()).getString() + "@" + linenumber;
        printAsJson(functionName,t);
        SourceVaraible.clear();
        //taintedVariable.clear();
        MapOfTaintedVaraible.clear();
        isMayReach = 0;
        Iterator mIterator = MapOfVaraible.entrySet().iterator();
        while (mIterator.hasNext()) {
            Map.Entry mapElement = (Map.Entry) mIterator.next();
            List<String> l = ((List<String>) mapElement.getValue());
             l.clear();
        }
        MapOfVaraible.clear() ;
        MapVaraibleLineNumber.clear();
        MapVaraibleLineNumberBlock.clear();
        MapAliasVaraibleBlockNumber.clear();
    }
        if((n.getToken() == Token.NAME) && n.getString() == sourceFunction)
        {
            findRetSourceVaraible(n);
        }

     //whatever source varaible found from retsource check if they are used in other variable or structure.
        for (int i = 0; i < SourceVaraible.size(); i++) {
            retInput = SourceVaraible.get(i);
            if (n.getToken() == Token.NAME && n.getString() == retInput ) {
                //wrting for struture kind
                checkWhichStructVarContainThisVar(n);
            }
            else
            {
                List<String> l = MapOfVaraible.get(retInput);
                if (l != null) {
                    for (int j = 0; j < l.size(); j++) {
                        String otherNameCheck = l.get(j);
                        if (n.getToken() == Token.NAME && n.getString() == otherNameCheck ) {
                            //wrting for struture kind
                            checkWhichStructVarContainOtherVar(n,retInput);
                        }
                    }
                }
            }

        }
//If its node ehich is parameter to sink funtion then we call identify sink param
            if((n.getToken() == Token.NAME) && ((n.getParent()).getToken() == Token.CALL))
          {
              identifySinkParam(n);
          }

        }

 //identify arguements to sink function
      public void identifySinkParam(Node n){
            int blocklinenumberSink = 0;
            if (n.getString() != sinkFunction) { //Node is not sink function
                if (((n.getParent()).getFirstChild()).getToken() == Token.NAME &&
                        ((n.getParent()).getFirstChild()).getString() == sinkFunction) { //codition to check if Node is argument to sink function
                    strName = n.getString();

                    Node getBlocklineNumber = (n.getParent()).getFirstChild();

                    for (Node p = getBlocklineNumber.getParent(); p != null; p = p.getParent()) {
                        if(p.getToken() == Token.BLOCK)
                        {
                            blocklinenumberSink    = p.getLineno(); //stores the line number of block of sink function ( to identify may and must)
                            break;
                        }
                    }
                    int MayReach = checkMayReach(getBlocklineNumber); //checks if sink function is called under any condition
                    checkTaintedVaraibles(strName,blocklinenumberSink,MayReach); //checks whether the variable may or must reach
                }

            }
        }
      }
    }
