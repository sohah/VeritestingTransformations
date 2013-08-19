/*******************************************************************************
 * Copyright (c) 2010
 *     Andreas Engelbredt Dalsgaard
 *     Casper Jensen 
 *     Christian Frost
 *     KasperLuckow.
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
 *     Kasper Luckow <luckow@cs.aau.dk> - Initial implementation
 ******************************************************************************/
package gov.nasa.jpf.symbc.realtime.minepump.actuators;

import gov.nasa.jpf.symbc.realtime.minepump.legosim.lib.Motor;

public class WaterpumpActuator{
    protected boolean emergencyState;
    //private static final int SPEED = 70;

    protected Motor legomotor;
    
    public WaterpumpActuator(int id) {
    	this.legomotor = new Motor(id);        
        this.emergencyState = false;
    }

	// THE FOLLOWING CODE IS USED IN minepump.tex !!!!
    public synchronized void start() {
        //if (this.emergencyState == false) {
            //start();
        //}    
    }
    
    // THE PREVIOUS CODE IS USED IN minepump.tex !!!!

    public void stop() {
        //this.legomotor.setMotorPercentage(Motor.STATE_BRAKE, false, 100);
    }
    
    /**
     * Sets the current emergency stop state.
     *
     * If set to true, then the waterpump motor is not allowed to start, even
     * if start() is called, and the pump is stopped.
     * This mode is cancelled by by calling emergencyStop(false)
     */
    // THE FOLLOWING CODE IS USED IN minepump.tex !!!!
    public synchronized void emergencyStop(boolean performEmergencyStop) {
        //this.emergencyState = performEmergencyStop;
        if (performEmergencyStop == true) {
            //stop();
        }
    }
    // THE PREVIOUS CODE IS USED IN minepump.tex !!!!

}
