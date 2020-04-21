import { Component, OnInit, Output, EventEmitter } from '@angular/core';

@Component({
  selector: 'form-entry-term',
  templateUrl: './form-entry-term.component.html',
  styleUrls: ['./form-entry-term.component.css']
})
export class FormEntryTermComponent implements OnInit {
	public term: string;

	@Output() termValue = new EventEmitter<string>();
	@Output() previousPageValue = new EventEmitter<boolean>();
	@Output() skipValue = new EventEmitter<boolean>();
	
	constructor() { }

	ngOnInit() {
	}

	emitResponse() {
		this.termValue.emit(this.term);
	}

	emitBackResponse() {
		this.previousPageValue.emit(false);
	}

	emitSkipResponse() {
		this.skipValue.emit(true);
	}
}