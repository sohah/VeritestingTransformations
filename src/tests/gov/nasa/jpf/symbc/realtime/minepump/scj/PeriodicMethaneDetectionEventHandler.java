/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Jensen 
 *     uckow.
 * 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Public License v3.0
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/gpl.html
 * 
 * Contributors:
 *     Andreas Engelbredt Dalsgaard <andreas.dalsgaard@gmail.com> - Changes to run on  jop SCJ implementation
 *     Casper Jensen <semadk@gmail.com> - Initial implementation
 *     Christian Frost <thecfrost@gmail.com> - Initial implementation
 *     Kaspeuckow <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump.scj;

import gov.nasa.jpf.symbc.realtime.minepump.actuators.WaterpumpActuator;
import gov.nasa.jpf.symbc.realtime.minepump.sensors.MethaneSensor;

import java.util.Random;

import javax.scj.PeriodicParameters;
import javax.scj.PeriodicThread;


public class PeriodicMethaneDetectionEventHandler extends PeriodicThread
{
	private MethaneSensor methaneSensor;
	private WaterpumpActuator waterpumpActuator;
	
	public PeriodicMethaneDetectionEventHandler(PeriodicParameters parameters,
	                                        MethaneSensor methaneSensor,
	                                        WaterpumpActuator waterpumpActuator)
	{
		super(parameters);
		this.methaneSensor = methaneSensor;
		this.waterpumpActuator = waterpumpActuator;
	}

	public static void main(String[] args) {
		int criticalMethaneLevel = 2;
		int brickHistorySize = 5;
		MethaneSensor m = new MethaneSensor(0, criticalMethaneLevel, brickHistorySize);
		
		WaterpumpActuator w = new WaterpumpActuator(0);
		PeriodicMethaneDetectionEventHandler l = new PeriodicMethaneDetectionEventHandler(
				new PeriodicParameters(2000),
					m, w);
		
		l.run();
	}

	@Override
	protected boolean run() {
		
		if(methaneSensor.isCriticalMethaneLevelReached())
	      	waterpumpActuator.emergencyStop(true);
		else
			waterpumpActuator.emergencyStop(false);
		return true;
	}
}
