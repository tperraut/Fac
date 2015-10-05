public class Ex3 extends Thread
{
	@Override
	public void run()
	{
		for (int i = 0; i < 10; i++)
		{
			try{this.sleep(1000);}
			catch (Exception e) {}
			System.out.println("Bonjour");
		}
	}
	public static void main(String[] args)
	{
		Ex3 t = new Ex3();
		System.out.println("debut");
		t.start();
		try {
			t.join();
			sleep(2000);}
		catch (Exception e){};
		System.out.println("fin");
	}
}
