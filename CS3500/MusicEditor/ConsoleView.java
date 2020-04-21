package cs3500.music.view;

import java.util.ArrayList;
import cs3500.music.model.Note;
import cs3500.music.model.IMusicModel;
import cs3500.music.model.Pitch;


public class ConsoleView implements MusicView {

  IMusicModel<Note> model;

  ConsoleView(IMusicModel<Note> model) {
    this.model = model;
  }

  @Override
  public void initialize() {
    //empty
  }

  /**
   * Prints out textual representation of the music to the console
   */
  @Override
  public void displayView() {
    System.out.print(this.printMusic());
  }

  /**
   * @return the first line of the music piece, all the pitches
   */
  public String printFirstLine() {
    // adds all the notes to a list
    StringBuilder result = new StringBuilder();


    // gets the width of the largest beat, i.e. 1000 has a width of 4
    int maxBeatWidth = String.valueOf(this.model.getDuration()).length();

    // add a space
    for (int i = 0; i < maxBeatWidth; i++) {
      result.append(" ");
    }

    // print the first line of all the pitches
    for (int i = this.model.getLowestPitch(); i <= this.model.getHighestPitch(); i++) {
      Pitch pitch1 = Pitch.findPitch(i % 12);

      int octaveValue = (int) Math.floor(i / 12);
      String pitchString = pitch1.toString() + String.valueOf(octaveValue);
      int pitchStringLength = pitchString.length();

      result.append(this.printPitch(pitchStringLength, pitchString));
    }
    return result.toString() + "\n";

  }

  /**
   * @return the pitch printed as a string
   */
  public String printPitch(int pitchStringLength, String pitchString) {
    String result;
    switch (pitchStringLength) {
      case 2:
        result = "  " + pitchString + " ";
        break;
      case 3:
        result = " " + pitchString + " ";
        break;
      default:
        result = " " + pitchString;
        break;
    }
    return result;

  }

  /**
   * prints the music
   * @return
   */
  public String printMusic() {
    ArrayList<Note> listOfNote = this.model.retrieveAllNotes();
    StringBuilder allRow = new StringBuilder();

    // prints all the empty, white space
    String temp = "";
    for (int j = 0; j < (this.model.getHighestPitch() -
            this.model.getLowestPitch() + 1) * 5; j++) {
      temp += " ";
    }


    // prints the beat number on the left column from 0 to whatever
    int maxBeatWidth = String.valueOf(this.model.getDuration()).length();
    String beatNumber = "";
    for (int i = 0; i <= this.model.getDuration(); i++) {
      // prints space for the first line
      beatNumber = String.valueOf(i);
      while (beatNumber.length() < maxBeatWidth) {
        beatNumber = " " + beatNumber;
      }
      allRow.append(beatNumber + temp + "\n");
    }

    // prints the music notes (X, |)
    String tempFinal = allRow.toString();
    for (int beatWidth = 0; beatWidth < maxBeatWidth; beatWidth++) {
      int firstLineLength = this.printFirstLine().length();

      for (Note note : listOfNote) {
        char[] chars = tempFinal.toCharArray();
        int indexOfChar = maxBeatWidth + (note.getPitchValue() - this.model
                .getLowestPitch()) * 5;
        int rowNum_X = (firstLineLength) * (note.getStartBeat());
        chars[rowNum_X + indexOfChar + 2] = 'X';

        for (int m = 0; m <= note.getEndBeat() - note.getStartBeat() - 1; m++) {
          int rowNum = (firstLineLength) * (note.getStartBeat() + 1 + m);
          chars[rowNum + indexOfChar + 2] = '|';
        }
        tempFinal = String.valueOf(chars);
      }
    }

    return this.printFirstLine() + tempFinal;
  }
}
