import java.awt.*;
import java.io.File;
import javax.imageio.ImageIO;
import javax.swing.*;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.*;


public class look
{
	SimpleDateFormat formatter = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSSS");

	public void robo() throws Exception
	{
		Calendar now = Calendar.getInstance();
		Robot robot = new Robot();
		Dimension d = Toolkit.getDefaultToolkit().getScreenSize();
		//BufferedImage screenShot = robot.createScreenCapture(new Rectangle(Toolkit.getDefaultToolkit().getScreenSize()));
		BufferedImage screenShot = robot.createScreenCapture(new Rectangle(0, 0, d.width/2, d.height));
		ImageIO.write(screenShot, "JPG", new File("/home/philippe/"+formatter.format(now.getTime())+".jpg"));
		System.out.println(formatter.format(now.getTime()));
	}

	public static void main(String[] args) throws Exception
	{
		look s2i = new look();
		JFrame fenetre = new JFrame();
		Dimension d = Toolkit.getDefaultToolkit().getScreenSize();
		JLabel lab = new JLabel(new ImageIcon("/home/philippe/2015-02-04_16-05-35-0038.jpg"));
		lab.setBounds(0, 0, d.width/2, d.height);
		fenetre.getContentPane().add(lab);
		//Définit un titre pour notre fenêtre
		fenetre.setTitle("Ma première fenêtre Java K.K.");
		//Définit sa taille : 400 pixels de large et 100 pixels de haut
		fenetre.setSize(d.width/2, d.height);
		//Nous demandons maintenant à notre objet de se positionner au centre
		fenetre.setLocationRelativeTo(null);
		//Termine le processus lorsqu'on clique sur la croix rouge
		fenetre.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		//Et enfin, la rendre visible
		fenetre.setVisible(true);
		//	s2i.robo();
		//	Thread.sleep(100);
		//	s2i.robo();
		//	Thread.sleep(10000);
	}
}
