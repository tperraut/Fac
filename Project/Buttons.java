import java.util.*;

public class Buttons
{
	private HashMap<String, Rectangle> buttons;

	public Setbutton(String s, Rectangle r)
	{
		this.buttons = new HashMap<String, Integer[2]>;
		this.buttons.put(s, r);
	}
	public HashMap<String, Rectangle> get()
	{
		return (buttons);
	}
	public boolean add(String s,  Rectangle r)
	{
		if this.buttons.get(s) == null
		{
			this.buttons.put(s, r);
			return (true);
		}
		return (false);
	}
	public void remplace(String del, String add, Rectangle r)
	{
		this.buttons.remove(del);
		this.buttons.put(add, r);
		return ();
	}
}