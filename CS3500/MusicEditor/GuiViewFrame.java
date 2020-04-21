package cs3500.music.view;

import java.awt.*;
import java.awt.event.MouseListener; // Possibly of interest for handling mouse events

import javax.swing.*;

import cs3500.music.model.IMusicModel;
import cs3500.music.model.Note;

/**
 * A skeleton Frame (i.e., a window) in Swing
 */
public class GuiViewFrame extends javax.swing.JFrame implements MusicView {

  private final JPanel displayPanel;

  /**
   * Creates new GuiView
   */
  public GuiViewFrame(IMusicModel<Note> model) {
    super();
    this.displayPanel = new ConcreteGuiViewPanel(model);
    this.setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
    this.setResizable(false);
    this.setTitle("Music Editor");
    this.pack();
    this.setSize(1200, 500);

    JScrollPane scroll = new JScrollPane(displayPanel);
    this.getContentPane().add(scroll);
    this.setVisible(true);
  }

  /**
   * Allows the user to begin seeing the view.
   */
  @Override
  public void initialize(){
    this.setVisible(true);
  }

  @Override
  public void displayView() {
    //empty
  }



}
