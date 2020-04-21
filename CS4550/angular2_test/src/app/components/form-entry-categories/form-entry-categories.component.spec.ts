import { async, ComponentFixture, TestBed } from '@angular/core/testing';

import { FormEntryCategoriesComponent } from './form-entry-categories.component';

describe('FormEntryCategoriesComponent', () => {
  let component: FormEntryCategoriesComponent;
  let fixture: ComponentFixture<FormEntryCategoriesComponent>;

  beforeEach(async(() => {
    TestBed.configureTestingModule({
      declarations: [ FormEntryCategoriesComponent ]
    })
    .compileComponents();
  }));

  beforeEach(() => {
    fixture = TestBed.createComponent(FormEntryCategoriesComponent);
    component = fixture.componentInstance;
    fixture.detectChanges();
  });

  it('should create', () => {
    expect(component).toBeTruthy();
  });
});
