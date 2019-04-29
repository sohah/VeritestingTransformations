//package Launch;
package AnRocketLaunch;

enum ButtonState
{
    pressed, notPressed, inactive; //use upper case for enum values and constants
}
class Button
{
    ButtonState value;//inactive,pressed,not_pressed; inactive(default)
    public Button()
    {
        value = ButtonState.inactive;
    }
    public void activate()
    {
        value = ButtonState.notPressed;
    }
    public void reset() { value = ButtonState.inactive;}
    public void pressed() {value = ButtonState.pressed;}
    public ButtonState state()
    {
        return value;
    }
}
