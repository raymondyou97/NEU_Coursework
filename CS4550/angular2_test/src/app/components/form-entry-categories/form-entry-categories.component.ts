import { Component, OnInit, Output, EventEmitter } from '@angular/core';

@Component({
  selector: 'form-entry-categories',
  templateUrl: './form-entry-categories.component.html',
  styleUrls: ['./form-entry-categories.component.css']
})
export class FormEntryCategoriesComponent implements OnInit {
	public categories: string;

	@Output() categoriesValue = new EventEmitter<string>();
	@Output() previousPageValue = new EventEmitter<boolean>();
	@Output() skipValue = new EventEmitter<boolean>();
	
	constructor() { }

	ngOnInit() {
	}

	emitResponse() {
		this.categoriesValue.emit(this.categories);
	}

	emitBackResponse() {
		this.previousPageValue.emit(false);
	}

	emitSkipResponse() {
		this.skipValue.emit(true);
	}
}
