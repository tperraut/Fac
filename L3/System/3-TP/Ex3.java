public class Ex3 extends Thread
{
	@Override
	public void run()
	{
			try
			{
				for (int i = 0; i < 10; i++)
				{
					System.out.println("Bonjour");
					this.sleep(1000);
				}
			}
			catch (InterruptedException ex){
				System.out.println("thread interrupt");
			}
	}
	public static void main(String[] args)
	{
		Ex3 t = new Ex3();
		System.out.println("debut");
		t.start();
		try {
			sleep(2000);
			t.interrupt();
			t.join();
		}
		catch (Exception e){};
		System.out.println("fin");
	}
}
