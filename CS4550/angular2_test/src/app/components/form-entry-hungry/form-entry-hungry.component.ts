import { Component, OnInit, Output, EventEmitter } from '@angular/core';

@Component({
	selector: 'form-entry-hungry',
	templateUrl: './form-entry-hungry.component.html',
	styleUrls: ['./form-entry-hungry.component.css']
})
export class FormEntryHungryComponent implements OnInit {
	public hunger: boolean;

	@Output() hungerValue = new EventEmitter<boolean>();

	constructor() { }

	ngOnInit() {
	}

	emitResponse() {
		this.hungerValue.emit(this.hunger);
	}
}
