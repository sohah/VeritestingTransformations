/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Jensen 
 *     Christian Frost
 *     Kaspeuckow.
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
 *     Kauckow <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump.sensors;


public class HighWaterSensor {

	
	
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
		//Sensors.synchronizedReadSensors();
		
		//this probably has to be debugged :) especially the mysterious bit shift....
		//int sensorReading = Sensors.getBufferedSensor(this.sensorId)>> 1;
		//return sensorReading;
		return 0;
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
	
	protected int consecutiveReadingsTrigger;
	protected int consecutiveReadingsObserved;
	
	
	
	
	
	//calibrate me plz
	private static final int CURRENT_WATER_COLOR_THRESHOLD = 50;

	private int currentWaterColor;
	
	public HighWaterSensor(int sensorId, int consecWaterReadingsTrigger) {
		
		this.sensorId = sensorId;
		this.consecutiveReadingsTrigger = consecWaterReadingsTrigger;
		this.currentWaterColor = 0;
	}
	
	public boolean criticalWaterLevel() {
		int sensorReading = conductMeasurement();

		if(sensorReading > NO_BRICK_PRESENT){
			if(consecutiveReadingsObserved == 0) {
				this.currentWaterColor = sensorReading;
				consecutiveReadingsObserved++;
			}
			else if(sensorReading <= this.currentWaterColor + CURRENT_WATER_COLOR_THRESHOLD && 
			   sensorReading >= this.currentWaterColor - CURRENT_WATER_COLOR_THRESHOLD) {
				consecutiveReadingsObserved++;
			}
			else
				consecutiveReadingsObserved = 0;			
		}
		else
			consecutiveReadingsObserved = 0;
		if(consecutiveReadingsObserved >= consecutiveReadingsTrigger) {
			consecutiveReadingsObserved = 0;
			return true;
		}
		else return false;
	}
	
}
