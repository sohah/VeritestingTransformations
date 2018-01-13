
public class tcas_nonstatic {
    public  int OLEV = 600;
    public  int MAXALTDIFF = 300;
    public  int MINSEP = 600;
    public  int NOZCROSS = 100;

    public  int Cur_Vertical_Sep;
    public  boolean High_Confidence;
    public  boolean Two_of_Three_Reports_Valid;

    public  int Own_Tracked_Alt;
    public  int Own_Tracked_Alt_Rate;
    public  int Other_Tracked_Alt;

    public  int Alt_Layer_Value;

    int Positive_RA_Alt_Thresh_0;
    int Positive_RA_Alt_Thresh_1;
    int Positive_RA_Alt_Thresh_2;
    int Positive_RA_Alt_Thresh_3;

    public  int Up_Separation;
    public  int Down_Separation;

    public  int Other_RAC;

    public  int NO_INTENT = 0;
    public  int DO_NOT_CLIMB = 1;
    public  int DO_NOT_DESCEND = 2;

    public  int Other_Capability;
    public  int TCAS_TA = 1;
    public  int OTHER = 2;

    public  int Climb_Inhibit;

    public  int UNRESOLVED = 0;
    public  int UPWARD_RA = 1;
    public  int DOWNWARD_RA = 2;

    public  void initialize() {
        Positive_RA_Alt_Thresh_0 = 400;
        Positive_RA_Alt_Thresh_1 = 500;
        Positive_RA_Alt_Thresh_2 = 640;
        Positive_RA_Alt_Thresh_3 = 740;
    }

    public  int ALIM() {
        if (Alt_Layer_Value == 0){
            return Positive_RA_Alt_Thresh_0;
        }
        else if (Alt_Layer_Value == 1){
            return Positive_RA_Alt_Thresh_1;
        }
        else if (Alt_Layer_Value == 2){
            return Positive_RA_Alt_Thresh_2;
        }
        else{
            return Positive_RA_Alt_Thresh_3;
        }
    }

    public  int Inhibit_Biased_Climb() {
        if (Climb_Inhibit > 0) {
            int ret = Up_Separation + NOZCROSS;
            return ret;
        }
        else{
            return Up_Separation;
        }
    }

    public  boolean Non_Crossing_Biased_Climb() {
        int upward_preferred;
        int inhibit_biased_climb = Inhibit_Biased_Climb();
        if (inhibit_biased_climb > Down_Separation) {
            upward_preferred = 1;
        } else {
            upward_preferred = 0;
        }
        if (upward_preferred != 0) {
            int alim = ALIM();
            if(!(Down_Separation >= alim)){
                return true;
            }
            else{
                return false;
            }
        }
        else {
            if (!(Cur_Vertical_Sep >= MINSEP)){
                return false;
            }
            else{
                int alim = ALIM();
                if(!(Up_Separation >= alim)){
                    return false;
                }
                else{
                    boolean own_above_thread = Own_Above_Threat();
                    if (!own_above_thread){
                        return false;
                    }
                    else{
                        return true;
                    }
                }

            }
        }
    }

    public  boolean Non_Crossing_Biased_Descend() {
        int upward_preferred;
        int inhibit_biased_climb = Inhibit_Biased_Climb();
        if (inhibit_biased_climb > Down_Separation) {
            upward_preferred = 1;
        }
        else {
            upward_preferred = 0;
        }
        if (upward_preferred != 0) {
            int alim = ALIM();
            boolean own_below_threat = Own_Below_Threat();
            // reduction source
            if (!(Cur_Vertical_Sep >= MINSEP)){
                return false;
            }
            else if (!(Down_Separation >= alim)){
                return false;
            }
            else if (!own_below_threat){
                return false;
            }
            else{
                return true;
            }
        }
        else {
            int alim = ALIM();
            boolean own_above_threat = Own_Above_Threat();
            // reduction source
            if(!(Up_Separation >= alim)){
                return false;
            }
            else if(!own_above_threat){
                return false;
            }
            else{
                return true;
            }
        }
    }

    public  boolean Own_Below_Threat() {
        boolean ret = false;
        if(Own_Tracked_Alt < Other_Tracked_Alt){
            ret = true;
        }
        return ret;
    }

    public  boolean Own_Above_Threat() {
        boolean ret = false;
        if(Other_Tracked_Alt < Own_Tracked_Alt){
            ret = true;
        }
        return ret;
    }

    public  int alt_assign(){
        int alt_sep = UNRESOLVED;
        boolean need_upward_RA = false;
        boolean non_crossing_biased_climb = Non_Crossing_Biased_Climb();
        if(non_crossing_biased_climb){
            boolean own_below_threat = Own_Below_Threat();
            if(own_below_threat){
                need_upward_RA = true;
            }
        }
        boolean need_downward_RA = false;
        boolean non_crossing_biased_descend = Non_Crossing_Biased_Descend();
        if(non_crossing_biased_descend){
            boolean own_above_threat = Own_Above_Threat();
            if(own_above_threat){
                need_downward_RA = true;
            }
        }
        if (need_upward_RA){
            if(need_downward_RA){
                alt_sep = UNRESOLVED;
            }
            else{
                alt_sep = UPWARD_RA;
            }
        }
        else{
            if (need_downward_RA){
                alt_sep = DOWNWARD_RA;
            }
            else{
                alt_sep = UNRESOLVED;
            }
        }

        return alt_sep;
    }

    public  int alt_sep_test() {
        boolean enabled = false;
        boolean tcas_equipped = false;
        boolean intent_not_known = false;
        int alt_sep = UNRESOLVED;

        if(High_Confidence){
            if(Own_Tracked_Alt_Rate <= OLEV){
                if(Cur_Vertical_Sep > MAXALTDIFF){
                    enabled = true;
                }
            }
        }
        if(enabled){
            if(Other_Capability == TCAS_TA){
                tcas_equipped = true;
            }
            if(tcas_equipped){
                if(Two_of_Three_Reports_Valid){
                    if(Other_RAC == NO_INTENT){
                        intent_not_known = true;
                    }
                }
                if(intent_not_known){
                    alt_sep = alt_assign();
                }
            }
            else{
                alt_sep = alt_assign();
            }
        }

        return alt_sep;
    }

    public  void mainProcess(int a1, int a2, int a3, int a4, int a5,int a6, int a7, int a8, int a9, int a10, int a11, int a12) {
        initialize();
        Cur_Vertical_Sep = a1;
        if (a2 == 0) {
            High_Confidence = false;
        }
        else {
            High_Confidence = true;
        }
        if (a3 == 0) {
            Two_of_Three_Reports_Valid = false;
        }
        else {
            Two_of_Three_Reports_Valid = true;
        }

        Own_Tracked_Alt = a4;
        Own_Tracked_Alt_Rate = a5;
        Other_Tracked_Alt = a6;
        Alt_Layer_Value = a7;
        Up_Separation = a8;
        Down_Separation = a9;
        Other_RAC = a10;
        Other_Capability = a11;
        Climb_Inhibit = a12;

        alt_sep_test();
    }

    public static void main(String[] argv) {
        tcas_nonstatic t = new tcas_nonstatic();
        t.mainProcess(601, -1, 0, -1, 0, 0, 0, 301, 400, 0, 0, 1);
    }
}
