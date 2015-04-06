/*
 * Copyright (C) 2014, United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * Symbolic Pathfinder (jpf-symbc) is licensed under the Apache License, 
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 *        http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and 
 * limitations under the License.
 */

/**
 * 
 */
package gov.nasa.jpf.symbc.symexectree.visualizer;

import java.util.LinkedList;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.JPF;
import gov.nasa.jpf.symbc.symexectree.ASymbolicExecutionTreeListener;
import gov.nasa.jpf.symbc.symexectree.DefaultNodeFactory;
import gov.nasa.jpf.symbc.symexectree.NodeFactory;
import gov.nasa.jpf.symbc.symexectree.structure.SymbolicExecutionTree;

/**
 * @author Kasper S. Luckow <luckow@cs.aau.dk>
 *
 */
public class SymExecTreeVisualizerListener extends ASymbolicExecutionTreeListener {

	private String dotFileOutputPath;
	private AVisualizer dotPrinter;
	/**
	 * symbolic.visualiser.outputformat = [png|eps|dot|pdf|ps|svg]		(default: dot)
	 * symbolic.visualizer.basepath = <output_path>
	 */
	public SymExecTreeVisualizerListener(Config conf, JPF jpf	) {
		super(conf, jpf);
		this.dotFileOutputPath = conf.getString("symbolic.visualizer.basepath");
		if(this.dotFileOutputPath == null)
			throw new SymExecTreeVisualizerException("symbolic.visualizer.basepath has not been set");
		String outputFormat = conf.getString("symbolic.visualizer.outputformat", "dot");
		OUTPUT_FORMAT format = OUTPUT_FORMAT.valueOf(outputFormat.toUpperCase());
		this.dotPrinter = new CompleteTreeVisualizer(format);
	}

	@Override
	protected NodeFactory getNodeFactory() {
		return new DefaultNodeFactory();
	}

	@Override
	protected void processSymbExecTree(
			LinkedList<SymbolicExecutionTree> trees) {
		this.dotPrinter.prettyPrintSymTrees(trees, this.dotFileOutputPath);
	}
}
