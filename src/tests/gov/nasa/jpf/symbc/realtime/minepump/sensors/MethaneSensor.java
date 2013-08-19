/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Jensen 
 *     Christian Frost
 *   
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
 *     Kasper <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump.sensors;

import gov.nasa.jpf.symbc.Debug;


public class MethaneSensor {
	
	private int criticalMethaneLevel;
	private MeasurementHistory mHistory;
	private boolean detectBrick = true;
	
	
	protected static final int NO_BRICK_PRESENT = 120;
	protected static final int WATER_SENSOR_RANGE_BEGIN = 132;
	protected static final int WATER_SENSOR_RANGE_END = 146;
	protected static final int METHANE_SENSOR_RANGE_BEGIN = 147;
	protected static final int METHANE_SENSOR_RANGE_END = 160;
	
	protected int sensorId;
	
	public int getSensorId() {
		return sensorId;
	}
	public void setSensorId(int sensorId) {
		this.sensorId = sensorId;
	}
	
	protected int conductMeasurement() {
		/*Sensors.synchronizedReadSensors();
		
		//this probably has to be debugged :) especially the mysterious bit shift....
		int sensorReading = Sensors.getBufferedSensor(this.sensorId)>> 1;
		return sensorReading;
		*/
		return 0;
		//return Debug.makeSymbolicInteger("SYMB");
	}

	protected boolean isBrickWater(int color) {
		return color >= WATER_SENSOR_RANGE_BEGIN && color <= WATER_SENSOR_RANGE_END;
	}
	
	protected boolean isBrickMethane(int color) {
		return color >= METHANE_SENSOR_RANGE_BEGIN && color <= METHANE_SENSOR_RANGE_END;
	}

	protected boolean isSensorReadingEnvironment(int color) {
		return !isBrickMethane(color) && !isBrickWater(color);
	}
	
	
	
	
	
	public MethaneSensor(int sensorId, int criticalMethaneLevel, int historySize) {
		this.sensorId = sensorId;
		
		this.criticalMethaneLevel = criticalMethaneLevel;
		this.mHistory = new MeasurementHistory(historySize);
	}
	
	// THE FOLLOWING CODE IS USED IN minepump.tex !!!!
	public boolean isCriticalMethaneLevelReached() {
		int sensorReading = conductMeasurement();
		//System.out.println("Methaneensor: " + sensorReading);
		if(isBrickMethane(sensorReading) && detectBrick == true)	
		{
			mHistory.addMeasurement(0);
			detectBrick = false;
			//System.out.println("GAS from methanesensor: " + sensorReading);
		}
			
		else if(isBrickWater(sensorReading) && detectBrick == true)
		{
			mHistory.addMeasurement(1);
			detectBrick = false;
			//System.out.println("WATER from methanesensor: " + sensorReading);
		}
		else
		{
			detectBrick = true;
		}
		return mHistory.getMethaneLevel() >= this.criticalMethaneLevel;
	}
	// THE PREVIOUS CODE IS USED IN minepump.tex !!!!

	
	private class MeasurementHistory {
		private int INSERT_POINT = 0;
		private int[] history;
		private int maxSize;
		
		public MeasurementHistory(int maxSize) {
			this.history = new int[maxSize];
			this.maxSize = maxSize;
			
			// Initialize to WATER as we are only tracking Methane
			for (int iter = 0; iter < this.maxSize; iter++) 
				this.history[iter] = 1;
			
		}
		
		public void addMeasurement(int brick) {			   
			this.history[this.INSERT_POINT] = brick;
			this.INSERT_POINT++;
			if (this.INSERT_POINT==history.length) {
				this.INSERT_POINT = 0;
			}
		}
		
		public int getMethaneLevel() {
			int methaneCount = 0;
			//@loopbound = 5
			for (int iter = 0; iter < this.maxSize; iter++) { 			
				if (this.history[iter] == 1) methaneCount++;			
			}
			
			return methaneCount;
		}
	}

}
