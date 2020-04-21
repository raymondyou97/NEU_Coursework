package cs3500.music;

import cs3500.music.util.CompositionBuilder;
import cs3500.music.util.MusicReader;
import cs3500.music.view.MusicView;
import cs3500.music.model.*;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.NoSuchElementException;
import java.util.Scanner;

import javax.sound.midi.InvalidMidiDataException;
import javax.sound.midi.MidiUnavailableException;

public class MusicEditor {
  public static void main(String[] args) throws IOException, InvalidMidiDataException {
    CompositionBuilder<IMusicModel<Note>> builder = new MusicModel.Builder();
    Readable fileReader = null;
    Scanner input = new Scanner(System.in);
    String fileName;

    while(fileReader == null) {
      System.out.print("Enter a file name: ");
      try {
        fileName = input.next();
        fileReader = new FileReader(new File(fileName));
      } catch (FileNotFoundException f) {
        System.out.append("Try again: bad file name\n");
      } catch (NoSuchElementException n) {
        System.out.append("Try again: input a file name\n");
      }
    }
    IMusicModel<Note> model = MusicReader.parseFile(fileReader, builder);

    MusicView view = null;
    while(view == null) {
      System.out.print("\nEnter \"1 for console\", \"2 for gui\", or \"3 for midi\" " +
              "to choose a view: ");
      switch(input.next()) {
        case "1":
          try {
            view =  new MusicView.returnView(model).create("console");
          } catch (MidiUnavailableException e) {
            e.printStackTrace();
          }
          break;
        case "2":
          try {
            view =  new MusicView.returnView(model).create("gui");
          } catch (MidiUnavailableException e) {
            e.printStackTrace();
          }
          break;
        case "3":
          try {
            view =  new MusicView.returnView(model).create("midi");
          } catch (MidiUnavailableException e) {
            e.printStackTrace();
          }
          break;
        default:
          System.out.append("Not a view type, try again!");
      }
    }

    view.displayView();
  }
}
