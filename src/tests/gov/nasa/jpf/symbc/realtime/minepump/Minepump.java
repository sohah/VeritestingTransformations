/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Juckow.
 * 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Public License v3.0
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/gpl.html
 * 
 * Contributors:
 *     Andreas Engelbredt Dalsgaard <andreas.dalsgaard@gmail.com> - Changes to run on  jop SCJ implementation
 *     Casperuckow <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump;

import gov.nasa.jpf.symbc.realtime.minepump.actuators.WaterpumpActuator;
import gov.nasa.jpf.symbc.realtime.minepump.scj.PeriodicMethaneDetectionEventHandler;
import gov.nasa.jpf.symbc.realtime.minepump.scj.PeriodicWaterLevelDetectionEventHandler;
import gov.nasa.jpf.symbc.realtime.minepump.sensors.HighWaterSensor;
import gov.nasa.jpf.symbc.realtime.minepump.sensors.LowWaterSensor;
import gov.nasa.jpf.symbc.realtime.minepump.sensors.MethaneSensor;

import javax.scj.PeriodicParameters;
import javax.scj.RealtimeSystem;

/** 
 * Open questions
 *
 * Use of SCJAllowed, should all usable classes be annotated with it?
 * - Do we import classes from both scj and java.realtime namepsaces?
 *
 * Should we refactor our configuration?
 *
 * Determine the mission memory size and set it in MainMission.java
 */

public class Minepump {
	
	/*public void setUp() {}
	
    public void tearDown() {}

    public MissionSequencer getSequencer() {
    	StorageParameters sp =
            new StorageParameters(100000L, 1000L, 1000L); // TODO: Set memory size
        return new MainMissionSequencer(new PriorityParameters(10), sp);
    }*/

	
    /*private static final int PERIODIC_GAS_PERIOD = 56;
   	private static final int PERIODIC_WATER_PERIOD = 40;
   	private static final int SPORADIC_WATER_PERIOD = 40;

	private static final int GAS_PRIORITY = 10;
	private static final int WATER_PRIORITY = 10;
   	*/
   	private static final int ACTUATOR_ID_WATERPUMP = 0;
   	private static final int ACTUATOR_ID_ENVIRONMENT = 1;

	private static final int SENSOR_ID_METHANE = 0;
	private static final int SENSOR_ID_HIGH_WATER = 1;
	private static final int SENSOR_ID_LOW_WATER = 2;
	
	
	
	public static void main(String[] args) {
		
		
		
		
		// Actuators 
				WaterpumpActuator waterpumpActuator = new WaterpumpActuator(ACTUATOR_ID_WATERPUMP);
				//WaterpumpActuator environmentActuators = new WaterpumpActuator(ACTUATOR_ID_ENVIRONMENT);

				// Sensors
				int criticalMethaneLevel = 2;
				int brickHistorySize = 5;
				MethaneSensor methaneSensor = new MethaneSensor(SENSOR_ID_METHANE, criticalMethaneLevel, brickHistorySize);
				
				int consecutiveNoWaterReadings = 3;
				int consecutiveHighWaterReadings = 3;
				HighWaterSensor highWaterSensor = new HighWaterSensor(SENSOR_ID_HIGH_WATER, consecutiveHighWaterReadings);
				LowWaterSensor lowWaterSensor = new LowWaterSensor(SENSOR_ID_LOW_WATER, consecutiveNoWaterReadings);

				// Methane
				PeriodicMethaneDetectionEventHandler methane = new PeriodicMethaneDetectionEventHandler(
					new PeriodicParameters(2000),
					methaneSensor, waterpumpActuator);
				//methane.register();		
				
				// Water
				PeriodicWaterLevelDetectionEventHandler water = new PeriodicWaterLevelDetectionEventHandler(
					new PeriodicParameters(2000),	
					highWaterSensor,
					lowWaterSensor,
					waterpumpActuator);	

				// init system
				//environmentActuators.start();
		
				

		RealtimeSystem.start();
		
		
		
		
		
		
		
		
		
		
		/*
		
		new PeriodicMethaneDetectionEventHandler(parameters, methaneSensor, waterpumpActuator)
		
		
	    new SporadicPushMotor(
	    		new SporadicParameters(4,//BLUE
	    				4000,
	    				60),
	    		0);
	    new SporadicPushMotor(
	    		new SporadicParameters(2,//WHITE
	    				4000,
	    				60), 
	    		1);

		PeriodicMotorSpooler motorSpooler = new PeriodicMotorSpooler(
				new PeriodicParameters(4000));

		new PeriodicReadSensor(new PeriodicParameters(2000), motorSpooler);

		
		*/
		
		
		
		
		
		
		
		
		
		// Implementation specific registration of safelet
		// The setUp function is then invoked on the safelet, continued by a call to getSequencer.
		// The Sequencer is then responsible for running the missions, when finished, the tearDown
		// method is invoked and the app is terminated.
		//JopSystem.startMission(new Minepump());
	}

	public long immortalMemorySize() {
		// TODO Auto-generated method stub
		return 1000;
	}

}
